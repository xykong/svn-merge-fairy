#!/usr/bin/python
# Merge Fairy
import sys
import os

# load config file
script_path = os.path.dirname(sys.argv[0])
execfile(script_path + "/fairy_config.py")

import re
import cgi
import BeautifulSoup
import urlparse
import os.path
# import pdb
import shutil
import time
import smtplib
import tempfile
import threading
import BaseHTTPServer
import signal
from optparse import OptionParser

__all__ = ('fairy', 'MergeFairy')


# fairy singleton
fairy = None


def signal_handler(signal_number):
    """A decorator to set the specified function as handler for a signal."""

    def __decorator(function):
        signal.signal(signal_number, function)
        return function

    return __decorator


# ---------------------------------------------------------------------
# the integration fairy itself

class MergeFairy:
    """Merge Fairy

    The Merge fairy knows about a set of branches and their interdependencies.

    When a branch changes, it automatically recompiles that branch, sending
    mail on success of failure.  It also attempts to automatically merge changes
    mail on success of failure.  It also attempts to automatically merge changes
    into any dependent branches and build those branches.

    If any merge conflicts or build errors occur, the developer who made the
    change is notified and the merge fairy does not attempt to check in or merge additional changes
    until the developer resolves the issue and sends a specially formatted checkin mail.
    """

    def __init__(self):
        """Trivial constructor for the Merge Fairy"""
        self.branches = []  # list of branches the fairy manages
        self.dependencyMap = {}  # map between a base branch and a list of dependent branches
        self.branchMap = {}  # map between a branch URL and branch object
        self.pollinterval = 60  # default interval between polls of the source tree
        self.currentAction = ''
        urlparse.uses_relative.insert(0, 'svn')  # Teach urlparse about svn urls

    def doBuilds(self):
        for branch in self.branches:
            self.doBuildsForRevisions(branch, branch.getPendingRevisions())
            self.saveConfig()  # save changes to the state of the fairy to the config file

    def doBuildsForRevisions(self, branch, revisions):
        """Try to build the given set of revisions, doing automatic merges on dependant branches as appropriate"""
        try:
            lastRevision = len(revisions) > 0 and revisions[-1] or None
            for revision in revisions:
                printAndLog("Considering %d in %s" % (revision.number, branch.url))
                recipient = self.getRecipientEmail(revision)

                if revision != lastRevision and not branch.update(revision):
                    printAndLog("No changes for %d " % revision.number)
                    continue

                if revision == lastRevision and not branch.cleanUpdate(revision):
                    branch.lastBuildVersion = revision.number
                    printAndLog("No changes for %d " % revision.number)
                    continue

                args = {'number': revision.number, 'branch': revision.branch, 'dev': revision.dev}

                self.currentAction = "Building " + branch.url
                printAndLog(self.currentAction)
                buildSucceeded = (not actAsBuildFairy) or branch.buildCurrentVersion()
                branch.lastBuildVersion = revision.number
                self.buildSucceeded = buildSucceeded

                if not buildSucceeded:
                    # if the build failed, send mail to the developer who checked in and bail out
                    # it doesn't make sense to try build any subsequent revisions
                    printAndLog(buildFailMessage[1] % args)
                    self.sendMail(madMergeFairyEmail, [recipient], buildFailMessage[0], buildFailMessage[1] % args)
                    return False

                printAndLog("Build succeeded, new version = %d" % branch.lastBuildVersion)

                # see if this checkin resolves a past merge failure
                match = re.search("MERGES\s+[rR]?([0-9]+)", revision.description)
                if match:
                    self.handleManualResolution(branch, int(match.group(1)), recipient)

                # See if this resolves a merge conflict in this branch
                if revision.description.find("NOFAIRY") >= 0:
                    for dependency in self.dependencyMap.getDependencies(branch):
                        dependency.lastGoodMerge = revision.number
                    printAndLog("Skipping merge for r%s because of do-not-merge directive" % (revision.number))
                    continue

                    # send mail on success to the administrator for tracking purposes
                # self.sendMail(mergeFairyEmail, [adminEmail], buildSucceededMessage[0], buildSucceededMessage[1] % args)

                # attempt to automatically merge changes into each of the dependent branches
                for dependency in self.dependencyMap.getDependencies(branch):
                    failedMergedVersion = dependency.failedMergeVersion

                    if failedMergedVersion == -1:  # if no blocking revisions
                        (mergeOK, reason) = self.mergeRevision(dependency, revision)
                    else:
                        printAndLog("Blocked on auto-merging version %s by earlier merge failure %s" % (
                            revision.number, dependency.failedMergeVersion))

            return True
        finally:
            self.saveConfig()

    def getStartMergeVersion(self, dependency, endVersion):
        startVersion = dependency.lastGoodMerge
        if startVersion == -1 or startVersion > endVersion:  # assume we're otherwise up to date if not last merge version is specified
            startVersion = endVersion - 1
        return startVersion

    def getMergeCommand(self, dependency, endVersion):
        startVersion = self.getStartMergeVersion(dependency, endVersion)
        return "svn merge -r%d:%d %s" % (startVersion, endVersion, dependency.baseBranch.url)


    def handleManualResolution(self, branch, resolvedVersion, recipient):
        dependency = self.getDependencyBlockedByRevision(resolvedVersion)
        if not dependency:  # we couldn't find any branch needing a merge for the given revision
            self.sendMail(mergeFairyEmail, [recipient], resolveSkippedMessage[0], resolveSkippedMessage[1] % \
                          {'resolvedVersion': resolvedVersion})
        else:
            if dependency.dependentBranch != branch:
                # the user attempted to checkin a manual merge, but the branch is wrong.  Let them know.
                self.sendMail(mergeFairyEmail, [recipient], resolveWrongBranchMessage[0], resolveWrongBranchMessage[1] % \
                              {'resolvedVersion': resolvedVersion, 'checkinBranch': branch,
                               'dependentBranch': dependency.dependentBranch})
            else:
                # Record that the merge conflict has been resolved
                failedMergeVersion = dependency.failedMergeVersion
                dependency.lastGoodMerge = failedMergeVersion
                dependency.failedMergeVersion = -1
                dependency.failedMergeDev = None

                # if it does, try to merge all of the subsequent blocked revisions
                for blockedRevision in dependency.baseBranch.getPendingRevisions(failedMergeVersion + 1):
                    (mergeOK, reason) = self.mergeRevision(dependency, blockedRevision)
                    if not mergeOK:  # bail out if the merge failed
                        break
                self.sendMail(mergeFairyEmail, [recipient], resolveSucceededMessage[0],
                              resolveSucceededMessage[1] % {'resolvedVersion': resolvedVersion})
                self.sendMail(happyMergeFairyEmail, [groupRecipients], resolveSucceededMessage[0],
                              resolveSucceededMessage[1] % {'resolvedVersion': resolvedVersion})

    def getDependencyBlockedByRevision(self, version):
        for dependency in self.dependencyMap.getAllDependencies():
            if dependency.failedMergeVersion == version:
                return dependency
        return None

    def mergeRevision(self, dependency, revision):
        """Merge the specified revision.
        Return a pair (result, reason) where result is a boolean indicating whether
        the merge succeeded and reason is a human readable description of any failures."""
        try:
            if revision.description.find("NOFAIRY") >= 0:
                printAndLog("Skipping merge for r%s because of do-not-merge directive" % (revision.number))
                dependency.lastGoodMerge = revision.number
                return (True, "No Fairy directive")
            dependentBranch = dependency.dependentBranch

            # first make sure the dependent branch is up to date
            if not self.doBuildsForRevisions(dependentBranch, dependentBranch.getPendingRevisions()):
                return (False, "build bad")

            self.currentAction = 'Merging r' + str(revision.number)
            recipient = self.getRecipientEmail(revision)

            args = {'number': revision.number, 'branch1': revision.branch, 'branch2': dependentBranch,
                    'dev': revision.dev, 'startVersion': self.getStartMergeVersion(dependency, revision.number)}

            # try merging
            mergeCmd = self.getMergeCommand(dependency, revision.number)
            (fChanged, fConflicted, conflictMessage) = dependentBranch.mergeChanges(mergeCmd)
            args['mergeCmd'] = mergeCmd

            # if a merge conflict occured, notify and rollback 
            if fConflicted:
                args['conflictMessage'] = conflictMessage
                printAndLog(mergeConflictMessage[1] % args)
                self.sendMail(madMergeFairyEmail, [recipient], mergeConflictMessage[0], mergeConflictMessage[1] % args)
                if groupRecipients:
                    self.sendMail(madMergeFairyEmail, [groupRecipients], mergeConflictMessage[0],
                                  mergeConflictMessage[1] % args)
                dependency.failedMergeVersion = revision.number
                dependency.failedMergeDev = revision.dev
                dependentBranch.prevSyncVersion = dependentBranch.lastSyncVersion
                dependentBranch.revertChanges()
                return (False, "conflicted")

            # otherwise try building
            elif fChanged:

                self.currentAction = "Building " + dependentBranch.url
                buildSucceeded = dependentBranch.buildCurrentVersion()

                if buildSucceeded:
                    # try commiting.  This might fail if the tree has changed from underneath us.
                    commitMessage = mergeBuildSucceededMessage[0] % args + "\n\n" + mergeBuildSucceededMessage[1] % args
                    commitMessage += '\n' + '_' * 80 + '\n' + revision.description
                    commitSucceeded = dependentBranch.commitChanges(commitMessage)

                    if commitSucceeded:
                        dependency.lastGoodMerge = revision.number

                        self.sendMail(mergeFairyEmail, [groupRecipients], mergeBuildSucceededMessage[0] % args,
                                      mergeBuildSucceededMessage[1] % args)
                        return (True, "succeeded")
                    else:
                        # whoops, the tree changed out from underneath us.
                        # roll back the changes and try again
                        dependentBranch.revertChanges()
                        return self.mergeRevision(dependency, revision)
                else:
                    # if a build or unit test failure occurred, notify and rollback 
                    dependency.failedMergeVersion = revision.number
                    dependency.failedMergeDev = revision.dev
                    dependentBranch.revertChanges()
                    self.sendMail(madMergeFairyEmail, [recipient], mergeBuildFailedMessage[0],
                                  mergeBuildFailedMessage[1] % args)
                    if groupRecipients:
                        self.sendMail(madMergeFairyEmail, [groupRecipients], mergeBuildFailedMessage[0],
                                      mergeBuildFailedMessage[1] % args)
                return (False, "failed")
            else:
                printAndLog("No changes")
                dependency.lastGoodMerge = revision.number

            return (True, "unchanged")
        finally:
            self.saveConfig()

    def printBanner(self):
        printAndLog("-" * 40)
        printAndLog("MERGE FAIRY")
        printAndLog("Running against branches:")
        for branch in self.branches:
            printAndLog("%s" % (branch))

    def sendMail(self, fromaddr, toaddrs, subject, msg):
        server = smtplib.SMTP(smtpServer)
        if smtpUserName and smtpPassword:
            if smtpUserName != "":
                server.login(smtpUserName, smtpPassword)
        server.set_debuglevel(1)
        fullMessage = "From: %s\nTo: %s\nSubject: %s\n\n%s" % (fromaddr, ", ".join(toaddrs), subject, msg)
        server.sendmail(fromaddr, toaddrs, fullMessage)
        server.quit()

    def getRecipientEmail(self, revision):
        if options.force_email:
            recipient = options.force_email
        else:
            recipient = revision.dev + domain
        return recipient

    def doMainLoop(self):
        self.printBanner()
        # pdb.set_trace()
        # go in a loop looking for changes that need to be built and merged                
        while True:
            try:
                self.doBuilds()
                if options.interactive:
                    raw_input('Press Enter to run')
                else:
                    self.currentAction = 'Waiting for work'
                    time.sleep(self.pollinterval)
            except KeyboardInterrupt:
                sys.exit(0)


    def getBranch(self, url):
        """Return the branch object corresponding to the given URL"""
        try:
            return self.branchMap[urlparse.urljoin(self.urlbase, url)]
        except:
            printAndLog("Error in configuration file: Unknown branch " + url)
            raise

    def loadConfig(self, configPath):
        "Initialize the state of the fairy from XML config files"
        self.configPath = os.path.join(os.path.dirname(os.path.abspath(sys.argv[0])), configPath)
        printAndLog("Merge Fairy loading configuration file " + self.configPath)

        soup = BeautifulSoup.BeautifulSOAP(open(self.configPath))
        dom = soup.first("fairy")

        for attr in ["urlbase", "pathbase", "buildcmd"]:
            self.__dict__[attr] = dom[attr]
        self.pollinterval = int(float(dom["pollinterval"]))

        self.branches = []
        self.branchMap = {}  # map between URLs and branch objects
        for branchNode in dom.fetch("branch"):
            branch = SvnBranch(self.buildcmd, urlbase=self.urlbase, pathbase=self.pathbase).initFromXml(branchNode)
            self.branches.append(branch)
            self.branchMap[branch.url] = branch
        self.branches.sort(key=lambda b: b.url)

        self.dependencyMap = DependencyMap()
        for dependencyNode in dom.fetch("dependency"):
            dependency = Dependency().initFromXml(dependencyNode, self)
            self.dependencyMap.addDependency(dependency)

    def saveConfig(self, configPath=None):
        """Persist the current state of the build fairy to the configuration XML file.
        The key change that is persisted is the last-merge-version attribute on
        dependencies. """

        if configPath == None:
            configPath = self.configPath

        # use a temporary file in case we blow up somewhere
        f = open(configPath + "_tmp", "w")
        f.write('<fairy '),
        for attr in ['urlbase', 'pathbase', 'pollinterval', 'buildcmd']:
            f.write('\n\t')
            f.write('%s="%s"' % (attr, self.__dict__[attr]))
        f.write('>\n\n')

        f.write(tabs(1) + '<branches>\n')
        for branch in self.branches:
            branch.writeXml(f, tabs(2))
        f.write(tabs(1) + '</branches>\n\n')

        self.dependencyMap.writeXml(f, tabs(1))
        f.write('</fairy>')
        f.close()
        # move the temporary file on top of the real one
        shutil.move(configPath + "_tmp", configPath)


class Revision:
    """Tracks information about a subversion revision"""

    def __init__(self, branch, number, dev, date, description=""):
        self.__dict__.update(locals())  # copy constructor arguments to object

    def __str__(self):
        return 'r' + str(self.number)

    def __repr__(self):
        return 'r' + str(self.number)


class SvnBranch:
    """Represents a source tree branch including a subversion URL and filesystem path"""

    def __init__(self, buildcmd, url="", path="", urlbase="", pathbase="", lastBuildVersion=-1, lastSyncVersion=-1):
        self.__dict__.update(locals())  # copy constructor arguments to object
        self.prevSyncVersion = -1

    def initFromXml(self, branchNode):
        self.url = urlparse.urljoin(self.urlbase, branchNode["url"])
        self.path = os.path.join(self.pathbase, branchNode["path"])
        self.buildSucceeded = branchNode.get("buildsucceeded", True)
        self.lastBuildVersion = int(branchNode.get("lastbuildversion", -1))
        self.lastSyncVersion = int(branchNode.get("lastsyncversion", -1))

        printAndLog("Loaded branch %s lastBuildVersion=%d lastSyncVersion=%d" % (
            self.url, self.lastBuildVersion, self.lastSyncVersion))
        return self

    def pushdir(self):
        self.cwd = os.getcwd()
        os.chdir(self.path)

    def popdir(self):
        os.chdir(self.cwd)

    def getSvnInfoProperty(self, prefix):
        self.pushdir()
        for line in self.popen("svn info"):
            if options.verbose:
                print line
            match = re.search("^" + prefix + "\s*([0-9]+)", line)
            if match:
                return match.group(1)
        self.popdir()
        return 0

    def getPendingRevisions(self, startingVersion=None, endingVersion=None):
        """Return a list of revision numbers that need to be merged to bring the enlistment
        up to date"""

        revisions = []
        if startingVersion == -1 or endingVersion == -1:
            return revisions

        if startingVersion == None:
            if self.lastBuildVersion == -1:
                return revisions
            else:
                sv = self.lastBuildVersion + 1
        else:
            sv = startingVersion

        if endingVersion == None:
            ev = "HEAD"
        else:
            ev = str(endingVersion)
        print "getPendingRevisions: " + str(sv) + ":" + str(ev)

        cmd = "svn log -r%s:%s %s --stop-on-copy" % (sv, ev, self.url)

        revision = None
        for line in self.popen(cmd):
            match = re.match("^r([0-9]+) \| ([A-Za-z._]+) \| ([^|]+)", line)
            if match and match.group(1) is not None:
                number = int(str(match.group(1)))
                dev = match.group(2)
                date = match.group(3)
                revision = Revision(self, number, dev, date)
                revisions.append(revision)
            elif revision:
                revision.description += line
        return revisions

    @staticmethod
    def popen(cmd):
        if options.verbose:
            print "Running cmd: " + cmd
        (fin, fout) = os.popen4(cmd)
        return fout

    def update(self, revision):
        """Run svn update on directory"""
        fUpdated = False
        for line in self.popen('svn --username "%s"  --password "%s" -r %d update %s' % (
                svnUserName, svnPassword, revision.number, self.path)):
            if not re.match("^At revision.*", line) and not re.match("^----------------", line):
                printAndLog(line)
                fUpdated = True
        self.prevSyncVersion = self.lastSyncVersion
        self.lastSyncVersion = revision.number

        printAndLog("update returning %d" % fUpdated)
        return fUpdated

    def cleanUpdate(self, revision):
        """Remove enlistement and svn checkout again"""
        fUpdated = False
        fBuildProps = False

        # Copy build.properties to a temp file
        buildPropsPath = os.path.join(self.path, "build.properties")
        fBuildProps = os.path.exists(buildPropsPath)
        if fBuildProps == True:
            src = open(buildPropsPath)
            printAndLog("Backing up " + src.name)
            temp = tempfile.TemporaryFile()
            temp.write(src.read())
            src.close()

        # Remove all files (if they exist)
        try:
            shutil.rmtree(self.path)
        except:
            pass

        # Create new enlistment
        for line in self.popen("svn -r %d checkout %s %s" % (revision.number, self.url, self.path)):
            if not re.match("^At revision.*", line) and not re.match("^----------------", line):
                printAndLog(line)
                fUpdated = True

        # Restore build.properties
        if fBuildProps == True:
            target = open(buildPropsPath, 'w+b')
            printAndLog("Restoring " + target.name)
            temp.seek(0)
            target.write(temp.read())
            target.close()
            temp.close()

        self.prevSyncVersion = self.lastSyncVersion
        self.lastSyncVersion = revision.number

        printAndLog("Clean update returning %d" % fUpdated)
        return fUpdated

    def buildCurrentVersion(self):
        self.pushdir()
        buildSucceeded = False
        printAndLog("Building " + self.url)
        for line in self.popen(self.buildcmd):
            printAndLog(line)
            if line.find(buildSucceededText) >= 0:
                buildSucceeded = True
        if buildSucceeded:
            printAndLog("Build Succeeded")
        else:
            printAndLog("Build Failed")

        self.popdir()
        return buildSucceeded

    def buildPendingRevisions(self):
        """
        Try to build all of the pending revisions in this branch.
        Return (True, None) if all succeeded, or (False, revision)
        if "revision" failed.
        """
        revisions = self.getPendingRevisions()
        if len(revisions) == 0:
            printAndLog("No pending revisions for %s" % self)
        for revision in revisions:
            if not self.build(revision):
                return (False, revision)
        return (True, None)

    def mergeChanges(self, mergeCmd):
        """Merge changes up to the given revision..
        Return a tuple with the following 3 values:
        1. fChanged=whether any files have changed
        2. fConflicted=whether any merge conflicts occurred
        3. mergeCmd=the command used to do the merge
        """
        self.pushdir()
        printAndLog("Merging changes: " + mergeCmd)
        fChanged = False
        fConflicted = False
        conflictMessage = None
        for line in self.popen(mergeCmd):
            printAndLog(line)
            fChanged = True
            if re.match("^C ", line) or re.match("^svn:", line) or re.match("Skipped missing target:",
                                                                            line) or re.match(
                    "has different repository root", line):
                fConflicted = True
                conflictMessage = line
        self.popdir()
        return (fChanged, fConflicted, conflictMessage)

    def revertChanges(self):
        """Revert all changes to this branch"""
        cmd = "svn revert -R %s" % (self.path)
        for line in self.popen(cmd):
            pass
        if self.prevSyncVersion:
            self.lastSyncVersion = self.prevSyncVersion
        # blow away any files that don't belong in the tree
        # subversion does not remove added files when reverting a merge.
        # these can cause build errors later.
        cmd = "svn status %s" % (self.path)
        for line in self.popen(cmd):
            match = re.match(r'^\?\s+(.*)', line)
            if match:
                try:
                    os.remove(match.group(1))
                except:
                    pass
        return True

    def commitChanges(self, commitMessage):
        """Commit all changes to this branch"""
        printAndLog("Commiting changes to %s" % self)
        commitOk = True
        if not options.fake_commit:
            commitFile = tempfile.NamedTemporaryFile()
            commitFile.write(commitMessage)
            commitFile.flush()
            cmd = 'svn commit --username "%s"  --password "%s" -F "%s" %s' % (
                svnUserName, svnPassword, commitFile.name, self.path)
            printAndLog(cmd)
            for line in self.popen(cmd):
                printAndLog(line)
                if re.search("Commit failed", line):
                    commitOk = False
                pass
            commitFile.close()
        else:
            printAndLog("*********Skipping actual commit")
        return commitOk

    def writeXml(self, f, linePrefix=""):
        """Write an xml representation of the branch to the given file"""
        url = relativize(self.urlbase, self.url)
        path = relativize(self.pathbase, self.path)
        f.write(linePrefix)
        f.write('<branch url="%s" path="%s" ' % (url, path))
        f.write('%s="%s" ' % ("buildSucceeded", self.buildSucceeded))
        if self.lastBuildVersion != -1:
            f.write('%s="%s" ' % ("lastBuildVersion", self.lastBuildVersion))
        if self.lastSyncVersion != -1:
            f.write('%s="%s" ' % ("lastSyncVersion", self.lastSyncVersion))
        f.write('/>\n')


    def __str__(self):
        return self.url


class Dependency:
    """Represents a dependency between two subversion branches"""

    def __init__(self, baseBranch=None, dependentBranch=None):
        self.__dict__.update(locals())  # copy constructor arguments to object

    def initFromXml(self, node, branchContainer):
        self.baseBranch = branchContainer.getBranch(node["basebranch"])
        self.dependentBranch = branchContainer.getBranch(node["dependentbranch"])
        self.failedMergeVersion = int(node.get("failedmergeversion", -1))
        self.lastGoodMerge = int(node.get("lastgoodmerge", -1))
        self.failedMergeDev = (node.get("failedmergedev", None))
        printAndLog("Loaded dependency %s=>%s lastGoodMerge=%d failedMergeVersion=%d failedMergeDev=%s" % (
            self.baseBranch, self.dependentBranch, self.lastGoodMerge, self.failedMergeVersion, self.failedMergeDev))
        return self

    def writeXml(self, f, prefix=""):
        """Write an XML representation of this object"""
        urlbase = self.dependentBranch.urlbase
        f.write(tabs(2) + '<dependency')
        template = cr + prefix + tab + '%s="%s" '

        f.write(template % ('baseBranch', relativize(urlbase, self.baseBranch.url)))
        f.write(template % ('dependentBranch', relativize(urlbase, self.dependentBranch.url)))
        f.write(template % ('lastGoodMerge', self.lastGoodMerge))
        if self.failedMergeVersion != -1:
            f.write(template % ('failedMergeVersion', self.failedMergeVersion ))
            f.write(template % ('failedMergeDev', self.failedMergeDev ))
        f.flush()
        f.write('/>')
        f.write(cr)


class DependencyMap:
    """Maintains mappings between a set of base and dependent branches."""

    def __init__(self):
        self.map = {}

    def getAllDependencies(self):
        for source in self.map.keys():
            for dependency in self.getDependencies(source):
                yield dependency

    def getDependencies(self, source):
        "Return all dependency objects that have source as their baseBranch"
        if not self.map.has_key(source):
            self.map[source] = []
        return self.map[source]

    def getRootBranches(self):
        return set(self.map.keys()).difference(self.map.values())

    def addDependency(self, dependency):
        """Add a dependency between two branches.  startVersion
        will be used as the starting version to begin merging changes"""
        self.getDependencies(dependency.baseBranch).append(dependency)

    def writeXml(self, f, prefix=""):
        f.write(prefix + '<dependencies>\n')
        for d in self.getAllDependencies():
            d.writeXml(f, prefix + '\t')
        f.write(cr + prefix + '</dependencies>\n')

    def __str__(self):
        return str(self.map)

# ---------------------------------------------------------------------
# Text strings


subjectPrefix = "MERGE: "
subjectFailurePrefix = "FAILURE: "

# BUILD SUCCESS AND FAILURE
buildSucceededMessage = (subjectPrefix + "Merge fairy build succeeded",
                         """Merge Fairy Build succeeded

                         Revision %(number)s (by %(dev)s)
                         %(branch)s
                         """)

buildFailMessage = (subjectFailurePrefix + "Merge fairy build failed", """Build FAILED for your revision r%(number)s to %(branch)s..

Revision %(number)s (by %(dev)s)
%(branch)s 
""")


# AUTOMATIC MERGE RESULTED IN MERGE CONFLICT
mergeConflictMessage = (subjectFailurePrefix + "Merge fairy merge conflict",
                        """ERROR: Auto-integration Failed

                        The merge fairy was unable to do an automatic merge due to a merge conflict.

                        Conflicting File:   %(conflictMessage)s

                        Revision %(number)s (by %(dev)s)
                        %(branch1)s => %(branch2)s

                        If you are %(dev)s, please do the following
                        1. Perform a manual merge in the destination branch using
                                %(mergeCmd)s

                        2. Fix the build failure

                        3. Check in the fix and be sure to include the following text in your checkin mail:
                            MERGES %(number)s
                        """)

# MERGE REMINDER
mergeReminderMessage = (subjectPrefix + "Merge fairy merge reminder",
                        """
                        The merge fairy has been blocked from integrating another checkin
                        based on an earlier failed merge of one of your checkins.

                        Revision %(number)s (by %(dev)s)
                        %(branch1)s => %(branch2)s

                        Please do the merge yourself, resolve the problem, and check in the fix to the destination branch.
                        """)


# AUTOMATIC MERGE RESULTED IN BUILD FAILURE
mergeBuildFailedMessage = (subjectFailurePrefix + "Merge fairy integration failure",
                           """ERROR: Auto-integration Failed

                           The merge fairy was unable to do an automatic merge due to a build error.

                           Revision %(number)s (by %(dev)s)
                           %(branch1)s => %(branch2)s

                           Please do the following:

                           1. Perform a manual merge in the destination branch using
                                   %(mergeCmd)s

                           2. Fix the build failure

                           3. Check in the fix and be sure to include the following text in your checkin mail:
                               MERGES r%(number)s
                           """)

mergeBadHtml = """
<div class="mergeBlockage">
<h3>%(branch1)s => %(branch2)s</h3>
Blocked by <b> revision r%(number)s from %(dev)s</b> <br> <br>

Please do the following to merge the changes manually:  
<ol>
<li> Perform a manual merge in the destination branch using <br>
        <b>%(mergeCmd)s</b>

<li> Fix the build failure or merge conflict.

<li> Check in the fix and include the following text in your checkin mail:
    <b>MERGES r%(number)s</b>
</ol>
</div>
"""

mergeGoodHtml = """
<div class="mergeGood">
<h3>%(branch1)s => %(branch2)s</h3> Merge of %(lastGoodMerge)s successful.
</div>
"""

headerHtml = """
<html><title>%(title)s</title>
<h1>%(title)s</h1>
<style>
body {font-family: arial;}
li { margin-bottom: 1em;}
table {border: solid 1px silver; border-collapse: collapse;}
h2 {text-decoration: underline}
th {text-align: left}
.revision { text-align: right}
.mergeBlockage { background-color: #FFF0F0; border: red; width: 500px; margin-bottom: 0.5em}
h3 { font-size: 12pt; font-weight: normal; padding: 0px; margin: 0px;}
.mergeBlockage h3 { background-color: #FDD;}
.mergeGood { background-color: #F0FFF0; border: green; width: 500px; margin-bottom: 0.5em}
.mergeGood h3 { background-color: #DFD; padding-bottom: 0px}
</style>
"""




# SUCCESSFUL AUTOMATIC MERGE
mergeBuildSucceededMessage = (subjectPrefix + "Automatic merge of r%(number)s",
                              """The merge fairy automatically merged and checked in the following revision:

                              Revision %(number)s (by %(dev)s)
                              %(branch1)s => %(branch2)s
                              """)

# WARNING MESSAGES FOR MANUAL MERGES
resolveSucceededMessage = (subjectPrefix + "Manual resolution succeeded",
                           """The manual resolution of r%(resolvedVersion)s has been successfully applied.""")
resolveSkippedMessage = (subjectFailurePrefix + "Revision already merged",
                         """You specified MERGES r%(resolvedVersion)s in your checkin mail,
                         but the merge fairy were unable to find any branch requiring a manual merge for that revision.
                         No action was taken. Please double check the revision number and submit a new checkin mail if needed.""")
resolveWrongBranchMessage = (subjectFailurePrefix + "Incorrect branch for MERGES directive",
                             """You specified MERGES r%(resolvedVersion)s in your checkin mail,
                             but you checked into %(checkinBranch)s instead of %(dependentBranch)s.
                             No action was taken. Please double check the revision number and submit
                             a new checkin mail if needed.""")



# ---------------------------------------------------------------------
# helper function to log to a file and print 
logFile = open(logFileName, "a")
lastLogTime = time.localtime()


def printAndLog(msg):
    global lastLogTime
    if time.localtime() > lastLogTime:
        print "[" + time.strftime("%d %b %Y %H:%M:%S", time.localtime()) + "]\n"
    lastLogTime = time.localtime()
    print msg
    logFile.write(msg)
    logFile.write("\n")
    logFile.flush()


tab = '\t'


def tabs(n):
    return '\t' * n


cr = '\n'


def relativize(base, path):
    """Convert an absolute URL or file path to a relative one"""
    path = path.replace('\\', '/')
    return re.sub("^" + base, "", path)


class FairyHTTPHandler(BaseHTTPServer.BaseHTTPRequestHandler):
    def do_GET(self):
        path = query_string = ''
        if self.path.find('?') != -1:
            path, query_string = self.path.split('?', 1)
        else:
            query_string = ''
        try:
            self.respond(path, query_string)
        except:
            pass

    def do_POST(self):
        query_string = self.rfile.read(int(self.headers['Content-Length']))
        self.respond('', query_string)

    def respond(self, path, query_string):
        # We use the cgi module to parse the query string:
        print "responding"
        self.args = dict(cgi.parse_qsl(query_string))
        self.send_response(200, 'OK')
        self.send_header('Content-type', 'text/html')
        self.send_header('Pragma', 'no-cache')
        self.end_headers()
        f = self.wfile
        f.write(headerHtml % {'title': 'Merge Fairy Status'})
        f.write("<h2>Build Status</h2>")

        f.write('<b> Current Action: ' + fairy.currentAction + '</b><br><br>')

        f.write("<table border=1>")
        f.write("<tr><th>Branch</th><th>Last Build</th></tr>")
        for branch in fairy.branches:
            color = branch.buildSucceeded and '#F0FFF0' or 'FFF0F0'
            lb = branch.lastBuildVersion
            lb = int(lb) == -1 and "None" or str(lb)

            f.write('<tr><td>%s</td><td bgcolor="%s" class="revision">%s</td><tr>' % \
                    (branch, color, lb))
        f.write("</table>")
        f.write("<h2>Merge Status</h2>")

        dependencies = []
        for d in fairy.dependencyMap.getAllDependencies():
            dependencies.append(d)

        dependencies.sort(key=lambda d: d.baseBranch.url)
        for d in dependencies:
            failedMerge = d.failedMergeVersion

            args = {'dev': d.failedMergeDev,
                    'branch1': relativize(fairy.urlbase, str(d.baseBranch)),
                    'branch2': relativize(fairy.urlbase, str(d.dependentBranch)),
                    'lastGoodMerge': str(d.lastGoodMerge)}
            if failedMerge >= 0:
                args['number'] = failedMerge
                args['mergeCmd'] = fairy.getMergeCommand(d, failedMerge)
                f.write(mergeBadHtml % (args))
            else:
                f.write(mergeGoodHtml % (args))

        f.write("</body></html>")


def daemonize(stdout='/dev/null', stderr=None, stdin='/dev/null',
              pidfile=None, startmsg='started with pid %s'):
    """
        This forks the current process into a daemon.
        The stdin, stdout, and stderr arguments are file names that
        will be opened and be used to replace the standard file descriptors
        in sys.stdin, sys.stdout, and sys.stderr.
        These arguments are optional and default to /dev/null.
        Note that stderr is opened unbuffered, so
        if it shares a file with stdout then interleaved output
        may not appear in the order that you expect.
    """
    # Do first fork.
    try:
        pid = os.fork()
        if pid > 0: sys.exit(0)  # Exit first parent.
    except OSError, e:
        sys.stderr.write("fork #1 failed: (%d) %s\n" % (e.errno, e.strerror))
        sys.exit(1)

    # Decouple from parent environment.
    os.chdir("/")
    os.umask(0)
    os.setsid()

    # Do second fork.
    try:
        pid = os.fork()
        if pid > 0: sys.exit(0)  # Exit second parent.
    except OSError, e:
        sys.stderr.write("fork #2 failed: (%d) %s\n" % (e.errno, e.strerror))
        sys.exit(1)

    # Open file descriptors and print start message
    if not stderr: stderr = stdout
    si = file(stdin, 'r')
    so = file(stdout, 'a+')
    se = file(stderr, 'a+', 0)
    pid = str(os.getpid())
    sys.stderr.write("\n%s\n" % startmsg % pid)
    sys.stderr.flush()
    if pidfile: file(pidfile, 'w+').write("%s\n" % pid)

    # Redirect standard file descriptors.
    os.dup2(si.fileno(), sys.stdin.fileno())
    os.dup2(so.fileno(), sys.stdout.fileno())
    os.dup2(se.fileno(), sys.stderr.fileno())


def startstop(stdout='/var/log/merge-fairy.log', stderr='/var/log/merge-fairy.err', stdin='/dev/null',
              pidfile=pidFileDir + '/fairy.pid', startmsg='started with pid %s', action='start'):
    if action:
        try:
            pf = file(pidfile, 'r')
            pid = int(pf.read().strip())
            pf.close()
        except IOError:
            pid = None

        if 'stop' == action or 'restart' == action:
            if not pid:
                mess = "Could not stop, pid file '%s' missing.\n"
                sys.stderr.write(mess % pidfile)
                if 'stop' == action:
                    sys.exit(1)
                action = 'start'
                pid = None
            else:
                try:
                    while 1:
                        os.kill(pid, signal.SIGTERM)
                        time.sleep(1)
                except OSError, err:
                    err = str(err)
                    if err.find("No such process") > 0:
                        os.remove(pidfile)
                        if 'stop' == action:
                            print 'Stopped'
                            sys.exit(0)
                        action = 'start'
                        pid = None
                    else:
                        print str(err)
                        sys.exit(1)

        if 'start' == action:
            if pid:
                mess = "Start aborded since pid file '%s' exists.\n"
                sys.stderr.write(mess % pidfile)
                sys.exit(1)

            daemonize(stdout, stderr, stdin, pidfile, startmsg)
            return

        if 'status' == action:
            if not pid:
                sys.stderr.write('Status: Stopped\n')

            else:
                sys.stderr.write('Status: Running\n')
            sys.exit(0)

            # ---------------------------------------------------------------------

# argument parsing and initialization
if __name__ == "__main__":
    parser = OptionParser()
    parser.add_option("-C", action="store", dest="config_file_name", default="fairy.xml",
                      help="configuration file path")
    parser.add_option("-e", "--forceemail", action="store", dest="force_email",
                      help="(DEBUG ONLY) force all emails to go to the given address")
    parser.add_option("-v", "--verbose", action="store_true", dest="verbose",
                      help="display additional debugging information.")
    parser.add_option("-i", "--interactive", action="store_true", dest="interactive",
                      help="(DEBUG ONLY) wait for a keystroke between iterations rather than sleeping")
    parser.add_option("-f", "--fakecommit", action="store_true", dest="fake_commit",
                      help="(DEBUG ONLY) don't actually commit any changes")
    parser.add_option("-s", "--start", action="store_true", dest="start_daemon", help="start the fairy as a daemon")
    parser.add_option("-r", "--restart", action="store_true", dest="restart_daemon",
                      help="restart the fairy as a daemon")
    parser.add_option("-x", "--stop", action="store_true", dest="stop_daemon", help="stop the fairy as a daemon")

    (options, args) = parser.parse_args()
    cmd = ""
    if len(args) >= 1:
        cmd = args[0]
    if options.stop_daemon or cmd == "stop":
        print "****Stopping fairy"
        startstop(action="stop")
    if options.start_daemon or cmd == "start":
        startstop(action="start")
        print "***Starting fairy"
    if options.restart_daemon or cmd == "restart":
        print "****Restarting fairy"
        startstop(action="restart")

    fairy = MergeFairy()
    fairy.loadConfig(options.config_file_name)
    fairy.saveConfig()  # save normalized config file immediately

    def startWebServer():
        port = 8081
        print "****Starting web server on port %d" % (port)
        server_address = ('', port)
        httpd = BaseHTTPServer.HTTPServer(server_address, FairyHTTPHandler)
        httpd.serve_forever()

    httpThread = threading.Thread(target=startWebServer)
    httpThread.start()

    fairy.doMainLoop()
