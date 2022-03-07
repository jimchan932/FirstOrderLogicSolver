
from enum import Enum
import copy
import re
# the structure of a predicate is:
# name, arguments
# argument can be constant or variable

# the structure of clausal form
# is a list of predicate

# both predicate and clausal form have "Causes", two reasons

# the resulting predicate or clausal form from mgu should consist only of
# constants

# TODO: we separate
#  (1) a list of predicates (with constants) , e.g. L(tony, john)
#  (2) a list of clausal form (consisting of predicates with constants and var)
#  e.g. (~A(x), S(x), C(x))



# predicate: {name, argumentList, length}

# clausal form : {name, list of predicate } 

# we separate argument as constants and variable

# we first consider the calculation of MGU of predicate and clausal form

class VarType(Enum):
    Constant = 1
    Variable = 2

class FormType(Enum):
    Pred = 1
    Clause = 2
# argList: list of dictionary of argname and type
    
class Predicate:
    def __init__(self, name, argList, boolVal):
        self.name = name
        self.argList = argList  
        self.length = len(argList)
        self.boolVal = boolVal
    def __str__(self):
        if not self.boolVal:
            negativeSign = '!'
        else:
            negativeSign = ''
        return '%s%s(%s)' %  (negativeSign,self.name, ','.join([variable['name'] for variable in self.argList]))
class ClausalForm:
    def __init__(self, predicateList):
        self.predicateList = predicateList
        self.length = len(predicateList)
    def __str__(self):
        resultStr = ','.join([predicate.__str__() for predicate in self.predicateList])
        return resultStr
        
""" 
this method returns:
-- new clausal form( it may be a predicate only)
-- replacements made( e.g. x = mike)  iteration of arguments:  constants matches, then continue; if the iteration constants does not match, no MGU!!
-- reasons ?? 
"""
""" The return value will be of a triple tuple (NEW clausal form, replacement list (Tuple), Convertable ?) """
def getMostGeneralUnifier(predicate, clausalForm):
    for predicateIter in range(len(clausalForm.predicateList)):  # iterate through Clausal Form to DO STH for matching predicate name
        currentPredicate = clausalForm.predicateList[predicateIter]
        if predicate.name == currentPredicate.name:
           if predicate.boolVal != currentPredicate.boolVal:  # P, ~P OR Q => Q
               replacements = []
               # Now check if can transform to MGU
               for termIter in range(len(predicate.argList)):
                   #print(predicate.argList[termIter])
                   if(predicate.argList[termIter]['variable_type'] == VarType.Constant and currentPredicate.argList[termIter]['variable_type'] == VarType.Constant and currentPredicate.argList[termIter]['name'] != predicate.argList[termIter]['name']):
                       return [], [], False
                   if(predicate.argList[termIter]['variable_type'] == VarType.Constant
                      and currentPredicate.argList[termIter]['variable_type'] == VarType.Variable):
                       replacements.append((currentPredicate.argList[termIter]['name'], predicate.argList[termIter]['name']))
               resultMGU = copy.deepcopy(clausalForm.predicateList)
               del resultMGU[predicateIter]
               for predicate_i in resultMGU:
                   for variable_i in predicate_i.argList:
                       for (originalVarname, replacedVarname) in replacements:
                           if originalVarname == variable_i['name']:
                               variable_i['variable_type'] = VarType.Constant
                               variable_i['name'] = replacedVarname
               return ClausalForm(resultMGU), replacements, True
    return [], [], False           
        # if term

def isArgumentsEqual(predicate_1, predicate_2):
    for (argument1, argument2) in zip(predicate_1.argList, predicate_2.argList):
        if argument1 != argument2:
            return False
    return True
    
def simplifyDoubleClauses(clausalForm1, clausalForm2):
    predicate_1 = clausalForm1.predicateList[0]
    predicate_2 = clausalForm1.predicateList[1]
    predicate_3 = clausalForm2.predicateList[0]
    predicate_4 = clausalForm2.predicateList[1]
    if(predicate_1.name == predicate_3.name and isArgumentsEqual(predicate_1, predicate_3)
       and predicate_2.name == predicate_4.name and isArgumentsEqual(predicate_2, predicate_4)):
        if(predicate_1.boolVal == predicate_3.boolVal and predicate_2.boolVal != predicate_4.boolVal):
            return predicate_1
        if(predicate_1.boolVal != predicate_3.boolVal and predicate_2.boolVal == predicate_4.boolVal):
            return predicate_2
    if(predicate_2.name == predicate_3.name and isArgumentsEqual(predicate_2, predicate_3)
       and predicate_1.name == predicate_4.name and  isArgumentsEqual(predicate_1, predicate_4)):        
        if(predicate_2.boolVal == predicate_3.boolVal and predicate_3.boolVal != predicate_4.boolVal):
            return predicate_2
        if(predicate_2.boolVal != predicate_3.boolVal and predicate_3.boolVal == predicate_4.boolVal):
            return predicate_3
    else: return None # cannot simplify   

def matchPredicate(predicate_str):
    if(predicate_str[0] == '!'):
        predicate_str = predicate_str[1:]
        boolSign = False
    else:
        boolSign = True
    predicateName = re.search('\w+', predicate_str).group()
    arguments = re.search('(?<=\().*?(?=\))', predicate_str).group()
    argumentList = [arg.strip() for arg in re.split(',', arguments)]
    argumentDict = []
    for argument_i in argumentList:
        variable_list = ['u','v','w','x','y','z']
        if argument_i in variable_list:
            argumentDict.append({'name' : argument_i, 'variable_type' : VarType.Variable})
        else:
            argumentDict.append({'name' : argument_i, 'variable_type' : VarType.Constant})            
    return Predicate(predicateName, argumentDict, boolSign)


# Next, we need to create a class to record:
# List1 of predicates: this will further consist of its causes R[(List, x),(list, y)],
#    and its number in the list, and original line number if exists
# List2 of Clausal Forms: this willl further consist of its causes R[(List, x),(List, y)],
#    and its number in the list, and original line number if exists    
# to solve our problem, after we have exhaust all matches for list1 to list2,
# we determine from list1 if there is logical inconsistency in list1,
# if yes then we are right; if no then the logic is wrong.


"""
 List :          list of  
                 list of replacements (if any)
                 list of cause, a tuple ((list1, num1), (list2, num2))
                 line number (if any)


"""
class PredicateLogic:
    def __init__(self):
        self.solutionsStack = []
        self.lineNumberMapping = []
        self.predicateList = []
        self.clausalFormList = []
        self.numOfDisplayedSentences = 0
    def input(self):
        numOfInput = input()
        self.numOfDisplayedSentences = int(numOfInput)
        for i in range(int(self.numOfDisplayedSentences)):
            sentence = input()
            sentence = sentence.strip()
            if sentence[0] == '(' and sentence[len(sentence)-1] == ')':  # we need to match for a clausal form
                sentence = sentence[1:len(sentence)-1]
                r1 = re.compile(r'(?:[^,(]|\([^)]*\))+')                
                predicateList = r1.findall(sentence) # [predicate.strip() for predicate in re.split(',', sentence)]
                self.clausalFormList.append((ClausalForm(list(map(matchPredicate, predicateList))),((FormType.Pred, -1),(FormType.Clause,-1)), i+1, []))
                self.lineNumberMapping.append((FormType.Clause, len(self.clausalFormList)-1, i+1))
            else:
                self.predicateList.append((matchPredicate(sentence), ((FormType.Pred, -1),(FormType.Clause,-1)), i+1, []))
                self.lineNumberMapping.append((FormType.Pred, len(self.predicateList)-1, i+1))
    def printer(self):
       print("Predicate List: ")
       for i in range(len(self.predicateList)):
           if(self.predicateList[i][2] != -1):
               print('(%d): ' % self.predicateList[i][2], end='')            
           #if self.predicateList[i][1] != ():     
            #   print("R[%s, %s] " % (self.predicateList[i][1][0], self.predicateList[i][1][1]), end='')
           
           print("R{", end='')
           for(originalVarname, replacedVarname) in self.predicateList[i][3]:
               print('%s = %s' % (originalVarname, replacedVarname), end='')
               print(',', end='')
           print('} ', end='') 
           
           print(self.predicateList[i][0], end ='')
           print('%d' % int(self.predicateList[i][0].boolVal))

       print("Clausal Form List: ")
       for i in range(len(self.clausalFormList)):
           if(self.clausalFormList[i][2] != -1):
               print('(%d): ' % self.clausalFormList[i][2], end='')
           
           #if self.clausalFormList[i][1] != ():     
           #   print("R[%s, %s] " % (self.clausalFormList[i][1][0], self.clausalFormList[i][1][1]), end='')
           
           print("{", end='')
           for(originalVarname, replacedVarname) in self.clausalFormList[i][3]:
               print('%s = %s' % (originalVarname, replacedVarname), end='')
               print(',', end='')
           print('} ', end='')              
           
           print(self.clausalFormList[i][0])                  
       """
       Steps:
       for( iterate through list1 to induct with those in list2)
          if result is a predicate
             - convert to all constants, if has variable, and add to list1
          else 
             if result is a double clause
                 - check if we can match with list2
             - add to list2
       NOTE: the iteration stops when we have exhausted the inductions for all predicates in list1
       """
    def findAllSentences(self):
        predicateListCounter = 0
        while(predicateListCounter < len(self.predicateList)):
#              print("Predicate Iteration: %d" % predicateListCounter)
              clausalFormCounter = 0
              while(clausalFormCounter < len(self.clausalFormList)):
 #                 print("Clausal Form iteration: %d"% clausalFormCounter)
                  resultClausalForm, replacements, hasMGU = getMostGeneralUnifier(self.predicateList[predicateListCounter][0],
                                                                                  self.clausalFormList[clausalFormCounter][0])
                  if(hasMGU):
                      if(resultClausalForm.length == 1):
                          self.predicateList.append((resultClausalForm.predicateList[0],
                                                    ((FormType.Pred, predicateListCounter), (FormType.Clause,clausalFormCounter)), 
                                                     -1, replacements))
                      else:
                          if(resultClausalForm.length == 2):
                              for doubleClauseCounter in range(0, len(self.clausalFormList)-1):
                                  if self.clausalFormList[doubleClauseCounter][0].length == 2:
                                      resultDoubleClausePred = simplifyDoubleClauses(resultClausalForm,self.clausalFormList[doubleClauseCounter][0])
                                      if(resultDoubleClausePred != None):
                                          self.predicateList.append((resultDoubleClausePred,
                                                                    ((FormType.Clause, doubleClauseCounter),
                                                                     (FormType.Clause, clausalFormCounter)), -1, []))
                          self.clausalFormList.append((resultClausalForm,
                                                      ((FormType.Pred, predicateListCounter), (FormType.Clause,clausalFormCounter)),
                                                      -1, replacements))
                  clausalFormCounter = clausalFormCounter + 1         
              # continue to the next iteration
              predicateListCounter = predicateListCounter + 1
    def proveLogic(self):
        for iter1 in range(0, len(self.predicateList)-2):
            for iter2 in range(iter1+1, len(self.predicateList)-1):
                predicate1 = self.predicateList[iter1][0]
                predicate2 = self.predicateList[iter2][0]
                if(predicate1.name == predicate2.name and isArgumentsEqual(predicate1, predicate2) and predicate1.boolVal != predicate2.boolVal):
                   return (iter1, iter2)
        return (-1, -1)
    def findSteps(self, cause1, cause2):
        self.findStepsAuxiliary(FormType.Pred, cause1, FormType.Pred, cause2)
    def findStepsAuxiliary(self, predType1, cause1, predType2, cause2):
        
        if cause1 != -1:
           if predType1 == FormType.Pred:
               causePredicate = self.predicateList[cause1]               
               self.solutionsStack.append((predType1, causePredicate, cause1))
               self.findStepsAuxiliary(causePredicate[1][0][0], causePredicate[1][0][1], causePredicate[1][1][0], causePredicate[1][1][1])
           if predType1 == FormType.Clause:
               causePredicate = self.clausalFormList[cause1]
               self.solutionsStack.append((predType1, causePredicate, cause1))
               self.findStepsAuxiliary(causePredicate[1][0][0], causePredicate[1][0][1], causePredicate[1][1][0], causePredicate[1][1][1])        
        if cause2 != -1:
           if predType2 == FormType.Pred:
               causePredicate = self.predicateList[cause2]               
               self.solutionsStack.append((predType2, causePredicate, cause2))
               self.findStepsAuxiliary(causePredicate[1][0][0], causePredicate[1][0][1], causePredicate[1][1][0], causePredicate[1][1][1])
           if predType2 == FormType.Clause:
               causePredicate = self.clausalFormList[cause2]
               self.solutionsStack.append((predType2, causePredicate, cause2))
               self.findStepsAuxiliary(causePredicate[1][0][0], causePredicate[1][0][1], causePredicate[1][1][0], causePredicate[1][1][1])               
        else:
            return
    def printSolution(self):
        
        while(self.solutionsStack):
            currentPredicateType, currentPredicate, indexInPredicateList = self.solutionsStack.pop()  # it is of type (predType, causePredicate)
            self.numOfDisplayedSentences = self.numOfDisplayedSentences + 1
            self.lineNumberMapping.append((currentPredicateType, indexInPredicateList, self.numOfDisplayedSentences))
            causeSentenceLineNumber1 = -1
            causeSentenceLineNumber2 = -1
            for predType, indexInList, lineNumber in self.lineNumberMapping:
                if(currentPredicate[1][0][0] == predType and currentPredicate[1][0][1] == indexInList):
                    causeSentenceLineNumber1 = lineNumber
                if(currentPredicate[1][1][0] == predType and currentPredicate[1][1][1] == indexInList):
                    causeSentenceLineNumber2 = lineNumber

            print("(%d) " % self.numOfDisplayedSentences, end='')
            if(causeSentenceLineNumber1 != -1 and causeSentenceLineNumber2 != -1):
                print("R[%d, %d] " % (causeSentenceLineNumber1, causeSentenceLineNumber2), end='')
                print("{", end='')
                for(originalVarname, replacedVarname) in currentPredicate[3]:
                    print('%s = %s' % (originalVarname, replacedVarname), end='')
                    print(',', end='')
                print('} ', end='') 
            print(currentPredicate[0])         
        print("(%d) R[%d, %d] = []" % (self.numOfDisplayedSentences-2, self.numOfDisplayedSentences-1,  self.numOfDisplayedSentences))     
def main():
    inferenceProgram = PredicateLogic()
    inferenceProgram.input()

    inferenceProgram.findAllSentences()
#    inferenceProgram.printer()

    result = inferenceProgram.proveLogic()
    
    if(result != (-1,-1)):
        print("True")
    else:
        print("False")        
        return
    inferenceProgram.findSteps(result[0], result[1])
    inferenceProgram.printSolution()
main()

