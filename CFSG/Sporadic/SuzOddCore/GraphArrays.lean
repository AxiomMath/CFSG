module

public import CFSG.Sporadic.SuzOddCore.Text
public import Certificates.Data.CFSGNative.MonsterB.Co2Data

public section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Monster.B.Co2.Native

@[expose] def zWord : List Int := [9, 3, 8, 7, 5, 10, 4, 7, 8, 7, 4, 10, 5, 4, 9, 10]

@[expose] def zPower : Nat := 7

@[expose] def localStrongIdx : List Nat := [2, 3, 4, 5, 6, 7, 8, 9]

@[expose] def localBaseNat : List Nat := [0, 1, 2, 3]

@[expose] def localDerivs : Array (List Int) :=
  #[[], [], [], [], [], [], [], [], [-3, 5, 2], [-2, -7, 8, 2], [-10, -10, 9, 9, 10],
    [-9, -9, -10, 9, 9, 9, 9], [-9, -9, 10, 9, 9, 9], [-11, -11, -11, 13, 13, 11]]

@[expose] def sylowQuotWords : List (List Int) :=
  [[10, 11, 9, 12, 10, 10, 14, 11, 12, 12, 13, 12, 10, 11, 9, 12, 10, 10, 14, 11, 12, 12, 13, 12],
    [9, 11, 9, 9, 11, 9, 10, 10, 10, 11, 10, 12, 9, 11, 9, 9, 11, 9, 10, 10, 10, 11, 10, 12, 9,
      11, 9, 9, 11, 9, 10, 10, 10, 11, 10, 12, 9, 11, 9, 9, 11, 9, 10, 10, 10, 11, 10, 12],
    [9, 13, 12, 9, 10, 13, 13, 14, 12, 11, 9, 12],
    [10, 11, 9, 11, 12, 10, 12, 14, 10, 13, 10, 9, 10, 11, 9, 11, 12, 10, 12, 14, 10, 13, 10, 9],
    [13, 13, 14, 14, 9, 14, 11, 11, 13, 14, 13, 9]]

@[expose] def centerMeta : List (Nat × Nat × Nat) :=
  [(22880, 1, 0), (281, 1, 1), (281, 1, 2), (38, 3, 0), (38, 3, 1), (281, 3, 2), (38, 3, 0),
    (281, 3, 1), (38, 3, 2)]

@[expose] def fusionEntries : List (Nat × Nat × List Int × Nat) :=
  [(1, 0, [], 1), (5, 95, [2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2], 1)]

@[expose] def normEntries : List Nat := [3, 4]

@[expose] def normWords : List (List Int) :=
  [[], [1], [2], [3], [4], [5], [6], [7], [8], [2, 1], [3, 1], [4, 1], [5, 1], [6, 1], [7, 1],
    [8, 1], [1, 2], [2, 2], [3, 2], [4, 2], [6, 2], [7, 2], [1, 3], [2, 3], [3, 3], [4, 3], [5, 3],
    [6, 3], [7, 3], [8, 3], [1, 4], [2, 4], [3, 4], [4, 4], [5, 4], [6, 4], [7, 4], [8, 4], [1, 5]]

@[expose] def normalizingSiftWords : List (List (List Int)) :=
  [[[9, 9, 2, 4, 3, 1], [5, 5, 4, 7, 9, 4], [7, 8, 8, 5], [10], [], []],
    [[8, 2, 10, 4, 4, 2], [10, 3, 4, 6, 7, 4], [6, 9, 5, 6, 5], [10], [], []]]

@[expose] def graphRecords : List (List Nat) :=
  [[0, 1, 2, 3, 4, 5], [22880, 8505, 1152, 4, 1, 1], [5, 39, 5876, 22880, 22880, 22880]]

@[expose] def graphRoundCounts : List (List Nat) :=
  [[3, 4, 5, 5], [9, 20, 37, 39, 39], [64, 1857, 5770, 5876, 5876],
    [6153, 14500, 22864, 22880, 22880], [22880], [22880]]

def outerArr : Array Nat := hexTable 4 22880 0 graphOuterText

def localDomain : List Nat := (hexTable 4 280 0 graphLocalText).toList

def localRun (k : Nat) : Array Nat :=
  let b := graphLocalText.toUTF8
  Array.ofFn (n := 280) fun i => hexAt b (1120 + 840 * k + 3 * i.val) 3

@[expose] def localGenArrs : Array (Array Nat) := Array.ofFn (n := 8) fun k => localRun k.val

@[expose] def localStrongArrs : Array (Array Nat) :=
  Array.ofFn (n := 14) fun k => localRun (8 + k.val)

def centerFull (r : Nat) : Array Nat := hexTable 4 22880 (23090 * r) graphCenterText

def centerCompact (r : Nat) : Array Nat :=
  let b := graphCenterText.toUTF8
  Array.ofFn (n := 280) fun i => hexAt b (92360 * r + 91520 + 3 * i.val) 3

end CFSG.Sporadic.SuzOddCore
