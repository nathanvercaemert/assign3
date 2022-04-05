import sys
import heapq
import copy
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
# for printing
globalBacktracks = 0
globalSolutions = 0
globalSolutionStrings = []
# for determining conflicts
globalNumQueens = numQueens
# max number of solutions
globalMaxSolutions = 2 * globalNumQueens
globalMaxSwitch = False


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
    domains = []
    for i in range(queenCount):
        colDomain = set()
        for j in range(queenCount):
            colDomain.add(j)
        domains.append(colDomain)
    return domains


def nextDomainNotEmpty(domains, queensAssignedCopy):
    if not queensAssignedCopy[0]:
        # assigning the first queen but the domain is empty
        if domains[0] == set():
            return False
    for queen, domain in enumerate(domains):
        # print(queen)
        # print(domain)
        # if domain is empty and it's the next queen being assigned
        if domain == set() and (not queensAssignedCopy[queen]) and (queensAssignedCopy[queen - 1]):
            return False
    return True


def determineAssignment(domains, queensAssigned):
    # determine which column to assign (the low
    for queenIndex, isAssigned in enumerate(queensAssigned):
        if not isAssigned:
            queen = queenIndex
            break

    # get the lowest unassigned row for the queen
    row = -1
    for possibleRow in domains[queen]:
        if row == -1:
            row = possibleRow
        else:
            if possibleRow < row:
                row = possibleRow

    # return the index of the domain (the queen's column = queen) and the row to assign for that queen
    # this removes the assigned row from that queen's domain
    # return queen, row
    domains[queen].remove(row)
    return queen, row


def areDiagonal(queen, otherQueen, row, otherRow):
    if row == -1 or otherRow == -1:
        return False
    dx = abs(queen - otherQueen)
    dy = abs(row - otherRow)
    if dx == dy:
        return True
    return False


def makeSolutionString(queenLocationsCopy):
    queenLocationsCopyFlip = createSquareMatrix(numQueens, False)
    for queen, isAssignedToRow in enumerate(queenLocationsCopy):
        for row, isAssigned in enumerate(isAssignedToRow):
            if isAssigned:
                queenLocationsCopyFlip[row][queen] = True
    solutionString = ""
    for queenFlip in queenLocationsCopyFlip:
        for isAssignedToRowFlip in queenFlip:
            if isAssignedToRowFlip:
                solutionString += "1 "
            else:
                solutionString += "0 "
        solutionString += "\n"
    return solutionString


# FOR propagation
def forPropagate(domainsCopy, assignedQueen, assignedRow):
    domainsCopyCopy = copy.deepcopy(domainsCopy)
    for queen, domain in enumerate(domainsCopyCopy):
        # if it's the next queen being assigned
        if queen > assignedQueen:
            # remove the assigned row from the next domain
            domainsCopy[queen].discard(assignedRow)

            # remove diagonal conflicts from next domain
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
        if (not queensAssignedCopy[queen]) and (queen > assignedQueen):
            modified = False
            for row in domain:
                dx = abs(queen - assignedQueen)
                dy = abs(row - assignedRow)
                # remove rows that equal the assigned row
                # remove rows that are diagonally conflicting with assigned row
                if row == assignedRow or dx == dy:
                    modified = True
                    domainsCopy[queen].remove(row)
            if modified:
                # because the variable's domain was changed, add the arcs from its unassigned neighbors to the queue
                for neighbor, isAssigned in enumerate(queensAssignedCopy):
                    if (not isAssigned) and (not neighbor == queen):
                        arcQueue.append((neighbor, queen))

    # arcQueue is tuples of (neighbor, queen whose domain has been changed)
    while arcQueue:
        print(arcQueue)
        arc = arcQueue.popleft()
        neighbor = arc[0]
        alteredQueen = arc[1]
        neighborDomain = domainsCopy[neighbor]
        alteredQueenDomain = domainsCopy[alteredQueen]

        # make a copy of the neighbor domain so that we can both iterate and remove as we iterate
        neighborDomainIterationCopy = copy.deepcopy(neighborDomain)

        for neighborRow in neighborDomainIterationCopy:
            alteredQueenDomainHasSatisfyingValue = False
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


def onlyFirstAssigned(queensAssignedCopy):
    for queen, isAssigned in enumerate(queensAssignedCopy):
        if queen > 1 and isAssigned:
            return False
    if not queensAssigned[0]:
        return False
    return True

def isConflicting(queenLocationsCopy):
    global globalNumQueens

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

    return False


# backtrackSearch
def backtrackSearch(domains, queensAssigned, queenLocations):
    global globalAgorithm
    global globalBacktracks
    global globalSolutions
    global globalSolutionStrings
    global globalMaxSolutions
    global globalMaxSwitch

    global debug
    debug += 1

    # print(domains)
    # while there are no empty domains
    while nextDomainNotEmpty(domains, queensAssigned):

        # # assignments will always be valid for MAC because all values in all domains are conflict-free
        # if globalAgorithm == "MAC":
        #     globalBacktracks += 1

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
            continue
        # else:
            # globalBacktracks += 1


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
                for queen, domain in enumerate(domains):
                    print(queen)
                    print(domain)
                print(makeSolutionString(queenLocationsCopy))

            # if we haven't reached 2*N solutions
            if globalSolutions < globalMaxSolutions and not globalMaxSwitch:
                # save the solution string for printing
                solutionString = makeSolutionString(queenLocationsCopy)
                globalSolutionStrings.append((queenLocationsCopy, solutionString))
                # increment number of solutions
                globalSolutions += 1
                continue
            elif globalSolutions == globalMaxSolutions and not globalMaxSwitch:
                globalMaxSwitch = True
                continue
            else:
                doPrint()
                exit()

        # copy domains for propagating constraints
        domainsCopy = copy.deepcopy(domains)
        # propagate constraints through the copy of domains (either with FOR or MAC)
        # this removes possible assignments from the copy of domains
        if globalAgorithm == "FOR":
            forPropagate(domainsCopy, assignedQueen, assignedRow)
        else:
            macPropagate(domainsCopy, assignedQueen, assignedRow, queensAssignedCopy)

        # if nextDomainNotEmpty(domainsCopy, queensAssignedCopy) and not globalMaxSwitch and globalAgorithm == "FOR":
        if nextDomainNotEmpty(domainsCopy, queensAssignedCopy) and not globalMaxSwitch:
            # it was a valid assignment so increment backtracks
            globalBacktracks += 1
            # for queen, domain in enumerate(domainsCopy):
            #     print(queen)
            #     print(domain)
            # print(makeSolutionString(queenLocationsCopy))
        # if not globalMaxSwitch and globalAgorithm == "MAC":
        #     # it's always a valid assignment for MAC (no condition here) because propagation leaves only valid assignments
        #     globalBacktracks += 1

        backtrackSearch(domainsCopy, queensAssignedCopy, queenLocationsCopy)


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

backtrackSearch(domains, queensAssigned, queenLocations)

# if we didn't reach 2*N solutions
doPrint()
