module

public import CFSG.Sporadic.Co2Schreier.Arrays
public import Certificates.Data.CFSGNative.Schreier.Check
public import Certificates.Data.CFSGNative.Co3Schreier.Basic
public import Certificates.Data.CFSGNative.MonsterB.BinarySha
public meta import CFSG.Sporadic.Co2Schreier.Arrays
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.Co3Schreier.Basic
public meta import Certificates.Data.CFSGNative.MonsterB.BinarySha
public meta import CFSG.Certificates.InvariantMerge
public import CFSG.Certificates.InvariantMerge
public import Std.Data.HashMap

public section

namespace CFSG.LocalAnalysis.WeakClosure81.SporCo2

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Co2Cert
  CFSG.Sporadic.Schreier.Co3.Native

@[expose] def pairText : String :=
  include_str "../../../Certificates/Data/CFSGNative/Co2Schreier/co2-asch54-pair.txt"

@[expose] def pairSha : Nat :=
  0xb69c759406218a1dfb2315ccb9712537b12fd4c34e11cba940af5d7259a53b7b

@[expose] def pairAArrs : Array (Array Nat) :=
  Array.ofFn (n := 14) fun j => hexLine pairText.toUTF8 3 2300 j.val

@[expose] def pairBArrs : Array (Array Nat) :=
  Array.ofFn (n := 15) fun j => hexLine pairText.toUTF8 3 2300 (14 + j.val)

@[expose] def pairABase : List Nat := [1, 1007, 29, 1980, 1809, 0]

@[expose] def pairBBase : List Nat := [1, 546, 113, 1007, 78, 223, 1440, 74, 1111, 354]

@[expose] def finList2300 (b : List Nat) : List (Fin 2300) :=
  b.map fun x => ⟨x % 2300, Nat.mod_lt _ (by decide)⟩

@[expose] def pairABaseArr : Array Nat := ((finList2300 pairABase).map Fin.val).toArray

@[expose] def pairBBaseArr : Array Nat := ((finList2300 pairBBase).map Fin.val).toArray

@[expose] def pairALevels : Array Level := rawLevels 2300 pairAArrs pairABaseArr

@[expose] def pairBLevels : Array Level := rawLevels 2300 pairBArrs pairBBaseArr

@[expose] def ambLevels : Array Level := rawLevels 2300 co2StrongArrs co2BaseArr

@[expose] def pairWordA0 : List Int := [2, 5, -1, 7, -6, -19, -7]

@[expose] def pairWordA1 : List Int :=
  [7, 7, 19, 6, -7, -24, -21, 8, 4, 10, 22, 7, 5, 10, 16, 8, 7, 24, 8, 22, 16, 21, 8, -5, 13, 19,
    -2, 21, 2, 17, 1, 5, 18, 29, 11, 3, 21, 11, 8, 24, 7, 4, -21, 10, 7, 8, 22, 7, 5, 10, -2, 13,
    -2, 21, 2, 4, 25, 15, 13, 29, 26, 22, 25, 12, 1, 12, 6, 9, 8, 24, 7, 4, -21, 10, 7, 8, 22, 7, 5,
    10, -2, 13, -2, 21, 2, 4, 25, 15, 13, 29, 26, 22, 25, 12, 24, 7, -8, 22, 3, 11, 3, 21, 11, -21,
    10, 7, 8, 22, 7, 6, 2, 13, 17, 6, 7, 19, 21, 14, 16, 13, 18, 28, 2, 23, 11, 4, 3, 2, 19, 6, -7,
    1, 6, 11, 4, 12, 1, 8, 24, 7, 4, -21, 10, 7, 8, 22, 7, 5, 10, -2, 13, -2, 21, 2, 4, 25, 15, 13,
    29, 26, 22, 25, 12, -8, 18, -24, -21, 8, 4, 10, 22, 7, 6, 10, 22, 7, 5, -13, -8, -21, 22]

@[expose] def pairJointArrs : Array (Array Nat) := pairAArrs ++ pairBArrs ++ co2StrongArrs

@[expose] def pairShift (l : Int) : Int := if 0 < l then l + 29 else l - 29

@[expose] def pairJointWords : Array (List Int) :=
  Array.ofFn (n := 40) fun j =>
    if j.val < 29 then []
    else if j.val = 29 then pairWordA0
    else if j.val = 30 then pairWordA1
    else (co2WordArrs[j.val - 29]!).map pairShift

end CFSG.LocalAnalysis.WeakClosure81.SporCo2
