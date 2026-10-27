module

public import CFSG.Sporadic.SmallOddCore.HSData
public import CFSG.Sporadic.SmallOddCore.ClassSimple
public meta import CFSG.Sporadic.SmallOddCore.HSData
public meta import CFSG.Sporadic.SmallOddCore.ClassSimple
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic

public section

namespace CFSG.Sporadic.SmallOddCore

open CFSG.PSL3Four.Native CFSG.Sporadic.SmallOddCore.Native

@[expose] def hsC1Tabs : Array Tab :=
  Array.ofFn (n := 2) fun k => natArr (hsCentTbl (k.val + 6))

@[expose] def hsC1Invs : Array Tab := hsC1Tabs.map (invTab 3850)

@[expose] def hsC2Tabs : Array Tab :=
  Array.ofFn (n := 4) fun k => natArr (hsCentTbl (k.val + 13))

@[expose] def hsC2Invs : Array Tab := hsC2Tabs.map (invTab 3850)

@[expose] def hsQWords : List (List Nat) :=
  [[1, 1, 1, 1], [0, 0, 0, 0, 0], [1, 0, 0, 1, 0, 0], [0, 1, 0, 0, 1, 0],
    [1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 1], [1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0]]

@[expose] def hsQGens : Array Tab :=
  Array.ofFn (n := 6) fun j => wordTabS 3850 hsC1Tabs (hsQWords.getD j.val [])

@[expose] def hsDWords : List (List Nat) := [[0, 0, 1, 0], [3, 0, 3, 0]]

@[expose] def hsDGens : Array Tab :=
  Array.ofFn (n := 2) fun j => wordTabS 3850 hsC2Tabs (hsDWords.getD j.val [])

@[expose] def hsDInvs : Array Tab := hsDGens.map (invTab 3850)

@[expose] def hsDClassWords : List (List Nat) :=
  [[], [1, 1, 1, 0, 1, 1, 0, 1, 0], [1, 1, 0, 1, 1, 1, 0, 1, 0], [0], [1, 0], [1, 1, 0], [1]]

@[expose] def hsDClassSizes : List Nat := [1, 40, 40, 45, 72, 72, 90]

@[expose] def hsC1Enum : Enum := enumBFS 3850 hsC1Tabs 7680

@[expose] def hsQEnum : Enum := enumBFS 3850 hsQGens 64

@[expose] def hsC2Enum : Enum := enumBFS 3850 hsC2Tabs 2880

@[expose] def hsDEnum : Enum := enumBFS 3850 hsDGens 360

@[expose] def hsDOrbits : Array Enum :=
  Array.ofFn (n := 7) fun l => orbitBFS 3850 hsDGens hsDInvs
    (wordTabS 3850 hsDGens (hsDClassWords.getD l.val [])) 1000

end CFSG.Sporadic.SmallOddCore
