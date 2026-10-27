module

public import CFSG.Sporadic.HNOddCore.InvData
public import Certificates.Data.CFSGNative.YGroups.ExactCheck

public section

namespace CFSG.Sporadic.HNOddCore.InvData

open CFSG.YGroups.ModelNative

@[expose] def dataLines (s : String) : List String := (textLines s).drop 1

@[expose] def natsAt (s : String) (k : Nat) : Array Nat := parseNats ((dataLines s).getD k "")

@[expose] def linesOf (s : String) : Array (Array Nat) := ((dataLines s).map parseNats).toArray

@[expose] def intLinesOf (s : String) : Array (List Int) := ((dataLines s).map parseInts).toArray

@[expose] def f1Arr : Array Nat := natsAt f1Text 0

@[expose] def f4Arr : Array Nat := natsAt f4Text 0

@[expose] def f6Arr : Array Nat := natsAt f6Text 0

@[expose] def s1Perms : Array (Array Nat) := linesOf s1Text

@[expose] def s4Perms : Array (Array Nat) := linesOf s4Text

@[expose] def s6Perms : Array (Array Nat) := linesOf s6Text

@[expose] def o1Lists : Array (Array Nat) := linesOf o1Text

@[expose] def o6Lists : Array (Array Nat) := linesOf o6Text

@[expose] def clsLists : Array (Array Nat) := linesOf clsText

@[expose] def parRecs : Array (List Int) := intLinesOf parText

@[expose] def cstrongPerms : Array (Array Nat) := linesOf cstrongText

@[expose] def qPerms : Array (Array Nat) := linesOf qpermText

@[expose] def cparRecs : Array (List Int) := intLinesOf cparText

@[expose] def cleftTabs : Array (Array Nat) := linesOf cleftText

@[expose] def vparRecs : Array (List Int) := intLinesOf vparText

@[expose] def vleftTabs : Array (Array Nat) := linesOf vleftText

@[expose] def pgenPerms : Array (Array Nat) := linesOf pgenText

@[expose] def pleftTabs : Array (Array Nat) := linesOf pleftText

@[expose] def pconjPerms : Array (Array Nat) := linesOf pconjText

end CFSG.Sporadic.HNOddCore.InvData
