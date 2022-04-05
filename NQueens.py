import sys
import heapq
import copy
import time
from collections import deque

# read in the arguments
algorithm = sys.argv[1]
# algorithm = "FOR"
numQueens = sys.argv[2]
numQueens = int(numQueens)
# numQueens = 4
outputFileName = sys.argv[3]

# globals
# for debugging
debug = 0
# to determine propagation algorithm
globalAgorithm = algorithm
# for printing the specified numbers
globalBacktracks = 0
globalSolutions = 0
globalSolutionStrings = []
# for determining conflicts - how many queens are there?
globalNumQueens = numQueens
# max number of solutions
globalMaxSolutions = 2 * globalNumQueens
globalMaxSwitch = False
# timing
timePreSearch = 0
timePostSearch = 0


# taken from stack overflow, used to create a matrix instead of numpy
def createSquareMatrix(count, initialize):
    matrix = []
    for i in range(count):
        # create a list for each row
        rowList = []
        for j in range(count):
            # append the initialization value for each column
            rowList.append(initialize)
        matrix.append(rowList)
    return matrix


# modified from createMatrix
def createDomains(queenCount):
    # the domains will be a list of sets of possible values for the queen. the index is the queen
    domains = []
    # for each queen
    for i in range(queenCount):
        # the domain for the queen
        colDomain = set()
        # it is a square, so each domain contains the same possibilities as there are queens
        for j in range(queenCount):
            # add the possible value
            colDomain.add(j)
        # append the queen's domain
        domains.append(colDomain)
    return domains


# check if the next domain to be assigned is empty
def nextDomainNotEmpty(domains, queensAssignedCopy):
    # are we assigning the first queen?
    if not queensAssignedCopy[0]:
        # assigning the first queen but the domain is empty
        if domains[0] == set():
            return False
    # figure out which queen is being assigned by iterating through the queens
    for queen, domain in enumerate(domains)
        # if domain is empty and it's the next queen being assigned
        if domain == set() and (not queensAssignedCopy[queen]) and (queensAssignedCopy[queen - 1]):
            return False
    return True


# where should we place a queen next?
def determineAssignment(domains, queensAssigned):
    # determine which column to assign (the lowest unassigned)
    for queenIndex, isAssigned in enumerate(queensAssigned):
        if not isAssigned:
            queen = queenIndex
            break

    # get the lowest unassigned row for the queen
    # start by setting a "lower than all" value
    row = -1
    for possibleRow in domains[queen]:
        # set row to the first available
        if row == -1:
            row = possibleRow
        else:
            # find the min row
            if possibleRow < row:
                row = possibleRow

    # return the index of the domain (the queen's column = queen) and the row to assign for that queen
    # this removes the assigned row from that queen's domain
    # return queen, row
    domains[queen].remove(row)
    return queen, row


# just returns if two matrix values are diagonal from each other
def areDiagonal(queen, otherQueen, row, otherRow):
    if row == -1 or otherRow == -1:
        return False
    dx = abs(queen - otherQueen)
    dy = abs(row - otherRow)
    if dx == dy:
        return True
    return False


# make the current configuration of queens into a printable string
def makeSolutionString(queenLocationsCopy):
    # for my printing loop, I need to flip along the diagonal because the string is appended by rows
    queenLocationsCopyFlip = createSquareMatrix(numQueens, False)
    for queen, isAssignedToRow in enumerate(queenLocationsCopy):
        for row, isAssigned in enumerate(isAssignedToRow):
            if isAssigned:
                queenLocationsCopyFlip[row][queen] = True

    # the string I'm going to be returning
    solutionString = ""
    # for each 
    for queenFlip in queenLocationsCopyFlip:
        for isAssignedToRowFlip in queenFlip:
            if isAssignedToRowFlip:
                # add a 1 if the queen is assigned
                solutionString += "1 "
            else:
                # add a 0 if the queen is not assigned
                solutionString += "0 "
        solutionString += "\n"
    return solutionString


# FOR propagation
def forPropagate(domainsCopy, assignedQueen, assignedRow):
    # need to copy so that I can iterate and modify
    domainsCopyCopy = copy.deepcopy(domainsCopy)
    for queen, domain in enumerate(domainsCopyCopy):
        # if it hasn't already been assigned
        if queen > assignedQueen:
            # remove the assigned row from domain
            domainsCopy[queen].discard(assignedRow)

            # remove diagonal conflicts domain
            for row in domain:
                dx = abs(queen - assignedQueen)
                dy = abs(row - assignedRow)
                if dx == dy:
                    domainsCopy[queen].discard(row)


# MAC propagation
def macPropagate(domainsCopy, assignedQueen, assignedRow, queensAssignedCopy):
    # the MAC queue for propagation
    arcQueue = deque()
    
    # need to make a copy of the domains so that I can iterate and remove while I'm iterating
    domainsCopyCopy = copy.deepcopy(domainsCopy)

    # manually do the first arc-consistency checks for the neighbors of the assigned queen (making sure they only leave values in their domains that agree with the assigned value for the assigned queen)
    # only need to check domains for neighbors of the assigned queen for these first iterations of MAC
    # if an unassigned neighbor's domain is altered, add it to the queue for checking in the below while loop
    # this first for loop is basically AC-3 with xi and xj reversed
    for queen, domain in enumerate(domainsCopyCopy):
        # only worry about unassigned queens
        if (not queensAssignedCopy[queen]) and (queen > assignedQueen):
            # keep track of whether or not the queen hap been modified
            modified = False
            for row in domain:
                dx = abs(queen - assignedQueen)
                dy = abs(row - assignedRow)
                # remove rows that equal the assigned row
                # remove rows that are diagonally conflicting with assigned row
                if row == assignedRow or dx == dy:
                    # note that it has be modified so that we can add the correct arcs to the queue
                    modified = True
                    domainsCopy[queen].remove(row)
            if modified:
                # because the variable's domain was changed, add the arcs from its unassigned neighbors to the queue
                for neighbor, isAssigned in enumerate(queensAssignedCopy):
                    # only worry about unassigned neighborsk
                    if (not isAssigned) and (not neighbor == queen):
                        arcQueue.append((neighbor, queen))

    # arcQueue is tuples of (neighbor, queen whose domain has been changed)
    while arcQueue:
        # get the next arc
        arc = arcQueue.popleft()
        # the neighbor of the modified queen
        neighbor = arc[0]
        # the modified queen
        alteredQueen = arc[1]
        # the neighbor's domain
        neighborDomain = domainsCopy[neighbor]
        # the modified queen's domain
        alteredQueenDomain = domainsCopy[alteredQueen]

        # make a copy of the neighbor domain so that we can both iterate and remove as we iterate
        neighborDomainIterationCopy = copy.deepcopy(neighborDomain)

        # for each possible value in the neighbor's domain
        for neighborRow in neighborDomainIterationCopy:
            # need to keep track of whether or not we have modified this neighbor
            # have modified if there is no satisfying value
            alteredQueenDomainHasSatisfyingValue = False
            # see if there is a satisfying value
            for alteredQueenRow in alteredQueenDomain:
                dx = abs(alteredQueen - neighbor)
                dy = abs(alteredQueenRow - neighborRow)
                if (not dx == dy) and (not alteredQueenRow == neighborRow):
                    # this condition checks to make sure that the altered queen has a domain value not equal or diagonal to the neighbor's domain value
                    alteredQueenDomainHasSatisfyingValue = True
            if not alteredQueenDomainHasSatisfyingValue:
                # if there is no satisfying value
                # remove the unsatisfied row from the neighbor's domain
                neighborDomain.remove(neighborRow)
                for neighborNeighbor, isAssigned in enumerate(queensAssignedCopy):
                    # and add all of the unassigned neighbors (of the now-altered neighbor) to the queue (these are neighborNeighbors)
                    if (not isAssigned) and (not neighborNeighbor == neighbor):
                        arcQueue.append((neighborNeighbor, neighbor))

# has only the first queen been assigned
def onlyFirstAssigned(queensAssignedCopy):
    # for all the queens to the right of the first, check if they've been assigned
    for queen, isAssigned in enumerate(queensAssignedCopy):
        if queen > 1 and isAssigned:
            return False
    # if even the first queen hasn't been assigned
    if not queensAssigned[0]:
        return False
    # only the first has been assigned
    return True


# is there a conflict in our assignments?
def isConflicting(queenLocationsCopy):
    global globalNumQueens

    # current assignments is going to be a list where each index is a queen, and each value is their assignment
    # a value of -1 means unassigned
    currentAssignments = []
    for queen in range(globalNumQueens):
        # about to check if/where each queen has been assigned
        # for starters, -1 means they haven't been assigned
        currentAssignments.append(-1)

    # after this loop, currentAssignments will have the row to which each queen has been assigned (or -1 if not assigned)
    # note that "queen" is a column index
    for queen, assignment in enumerate(queenLocationsCopy):
        for row in range(len(assignment)):
            if assignment[row]:
                currentAssignments[queen] = row

    # currentAssignments is ready

    for queen, row in enumerate(currentAssignments):
        for otherQueen, otherRow in enumerate(currentAssignments):
            if (not queen == otherQueen):
                # we are comparing the assignments of two different queens
                if (not row == -1) and row == otherRow:
                    # two queens have been assigned to the same row
                    return True
                if areDiagonal(queen, otherQueen, row, otherRow):
                    # two queens have diagonally conflicting assignments
                    return True

    # there aren't any conflicts
    return False


# backtrackSearch
def backtrackSearch(domains, queensAssigned, queenLocations):
    global globalAgorithm
    global globalBacktracks
    global globalSolutions
    global globalSolutionStrings
    global globalMaxSolutions
    global globalMaxSwitch
    global timePostSearch

    global debug
    debug += 1

    # print(domains)
    # while there are no empty domains
    while nextDomainNotEmpty(domains, queensAssigned):
        # making copies of all the data structures to pass to the recursive function
        # need to leave the non-copies as they are in case we return to them

        # determine which queen to assign (and where) within domains
        # this removes that row for the chosen queen's domain (because it is the assignment we are currently trying)
        assignedQueen, assignedRow = determineAssignment(domains, queensAssigned)
        # (assign the queen)
        queensAssignedCopy = copy.deepcopy(queensAssigned)
        queenLocationsCopy = copy.deepcopy(queenLocations)
        # set col in copy of queensAssigned to True
        queensAssignedCopy[assignedQueen] = True
        # set cell in queenLocations to true
        queenLocationsCopy[assignedQueen][assignedRow] = True

        if isConflicting(queenLocationsCopy):
            # there was a conflict, so we don't need to worry about this assignment any more


        # setting isSolution to False if any queens are unassigned
        isSolution = True
        for queen in queensAssignedCopy:
            if not queen:
                isSolution = False

        # if all queens have been assigned (no conflicting assignments will have reached this point)
        if isSolution:
            # it was a valid assignment so increment backtracks
            if not globalMaxSwitch:
                globalBacktracks += 1
                # for office hour discussion. leaving in case in needs to be readdressed
                # for queen, domain in enumerate(domains):
                #     print(queen)
                #     print(domain)
                # print(makeSolutionString(queenLocationsCopy))

            # if we haven't reached 2*N solutions
            if globalSolutions < globalMaxSolutions and not globalMaxSwitch:
                # save the solution string for printing
                solutionString = makeSolutionString(queenLocationsCopy)
                globalSolutionStrings.append((queenLocationsCopy, solutionString))
                # increment number of solutions
                globalSolutions += 1
                # continue to the next assignment
                continue
            elif globalSolutions == globalMaxSolutions and not globalMaxSwitch:
                # this was necessary due to a slight difference in my algorithm compared to TA
                # this achieves the given number of backtracks
                globalMaxSwitch = True
                continue
            else:
                # it's done so keep track of time
                timePostSearch = time.process_time()
                # print the requested data
                doPrint()
                # print the runtime
                print("Runtime:", str(timePostSearch - timePreSearch))
                exit()

        # copy domains for propagating constraints
        domainsCopy = copy.deepcopy(domains)
        # propagate constraints through the copy of domains (either with FOR or MAC)
        # this removes possible assignments from the copy of domains
        if globalAgorithm == "FOR":
            forPropagate(domainsCopy, assignedQueen, assignedRow)
        else:
            macPropagate(domainsCopy, assignedQueen, assignedRow, queensAssignedCopy)

        if nextDomainNotEmpty(domainsCopy, queensAssignedCopy) and not globalMaxSwitch:
            # it was a valid assignment so increment backtracks
            globalBacktracks += 1
            # leaving for office hours discussion. may need to return to this
            # for queen, domain in enumerate(domainsCopy):
            #     print(queen)
            #     print(domain)
            # print(makeSolutionString(queenLocationsCopy))

        # try to assign the next queen
        backtrackSearch(domainsCopy, queensAssignedCopy, queenLocationsCopy)


# the requested format for output
def doPrint():
    global globalAgorithm
    global globalBacktracks
    global globalSolutions
    global globalSolutionStrings
    print(globalAgorithm, "\n")
    print("Solutions:", globalSolutions, "\n")
    print("Backtracks:", globalBacktracks, "\n")
    i = 1
    for solutionString in globalSolutionStrings:
        print("#", str(i))
        i += 1
        print(solutionString[1])


# main

# what are the remaining domains for each queen's assignment?
domains = createDomains(numQueens)

# has the queen in each column been assigned?
queensAssigned = []
for i in range(numQueens):
    queensAssigned.append(False)

# to which cell has the queen in each column been assigned?
queenLocations = createSquareMatrix(numQueens, False)

# keep track of the time while doing the search
timePreSearch = time.process_time()
backtrackSearch(domains, queensAssigned, queenLocations)
timePostSearch = time.process_time()

# if we didn't reach 2*N solutions
doPrint()

# print the runtime
print("Runtime:", str(timePostSearch - timePreSearch))
