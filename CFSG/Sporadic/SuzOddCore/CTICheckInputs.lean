module

public import CFSG.Sporadic.SuzOddCore.InvTCheck
public import CFSG.Sporadic.SuzOddCore.RestrictDefs
public import Certificates.Data.CFSGNative.PSL3Four.Basic
public meta import CFSG.Sporadic.SuzOddCore.InvTCheck
public meta import CFSG.Sporadic.SuzOddCore.RestrictDefs
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic

public section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.PSL3Four.Native

@[expose] def fixList (i : Nat) : List Nat := fixedList 1782 (tArr i)

@[expose] def kGens (i : Nat) : Array Tab := (invInnerGenArrs i).map (restrictArr (fixList i))

@[expose] def kInvs (i : Nat) : Array Tab := (kGens i).map (invTab (fixList i).length)

@[expose] def wordTab (m : Nat) (gs : Array Tab) (w : List Nat) : Tab :=
  w.foldr (fun j acc => comp m gs[j]! acc) (idTab m)

@[expose] def dGens : Array Tab :=
  Array.ofFn (n := 5) fun j =>
    commTab 42 (kGens 0)[1]! (kGens 0)[j.val + 2]! (kInvs 0)[1]! (kInvs 0)[j.val + 2]!

@[expose] def dInvs : Array Tab := dGens.map (invTab 42)

@[expose] def classWords : List (List Nat) :=
  [[], [0], [1], [4], [3, 0], [1, 1], [4, 4], [4, 1, 1, 0], [4, 3, 3, 0], [1, 1, 4, 0]]

@[expose] def classSizes : List Nat := [1, 2240, 4032, 1260, 1260, 4032, 315, 2880, 1260, 2880]

@[expose] def classRep (l : Nat) : Tab := wordTab 42 dGens (classWords.getD l [])

@[expose] def qWords : List (List Nat) :=
  [[1, 8, 1, 8], [6, 9, 9, 9], [9, 6, 9, 9], [1, 7, 4, 5, 7, 9], [2, 1, 8, 1, 2, 8],
    [3, 1, 8, 1, 8, 3]]

@[expose] def qGens : Array Tab :=
  Array.ofFn (n := 6) fun j => wordTab 54 (kGens 1) (qWords.getD j.val [])

@[expose] def enumOf (m : Nat) (gs : Array Tab) (bound : Nat) : Enum := enumBFS m gs bound

@[expose] def classOrbits : Array Enum :=
  Array.ofFn (n := 10) fun l => orbitBFS 42 dGens dInvs (classRep l.val) 5000

@[expose] def centInOK (m : Nat) (T gs Q : Array Tab) : Bool :=
  let idx := indexOf Q
  allBelow T.size fun k =>
    !(allBelow gs.size fun i => comp m T[k]! gs[i]! == comp m gs[i]! T[k]!) || found idx Q T[k]!

end CFSG.Sporadic.SuzOddCore
