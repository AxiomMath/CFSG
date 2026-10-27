module

public import CFSG.Sporadic.Schreier.Co3SylowCheckInputs
public import Certificates.Data.CFSGNative.MonsterB.BinarySha
public meta import CFSG.Sporadic.Schreier.Co3SylowCheckInputs
public meta import Certificates.Data.CFSGNative.MonsterB.BinarySha

public section

namespace CFSG.LocalAnalysis.WeakClosure81.SporCo3

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier.Co3
  CFSG.Sporadic.Schreier.Co3.Native

@[expose] def pairText : String :=
  include_str "../../../Certificates/Data/CFSGNative/Co3Schreier/co3-asch54-pair.txt"

@[expose] def pairSha : Nat :=
  0xd586e8c315558ce4623991eeaf9f29587ad38e985175536542d2f00c2ae96d38

@[expose] def pairAArrs : Array (Array Nat) :=
  Array.ofFn (n := 9) fun j => hexLine pairText.toUTF8 3 276 j.val

@[expose] def pairBArrs : Array (Array Nat) :=
  Array.ofFn (n := 10) fun j => hexLine pairText.toUTF8 3 276 (9 + j.val)

@[expose] def pairABase : List Nat := [0, 227, 154, 106]

@[expose] def pairBBase : List Nat := [0, 106, 200, 28, 55]

@[expose] def pairABaseArr : Array Nat :=
  ((co3FinList 276 (by decide) pairABase).map Fin.val).toArray

@[expose] def pairBBaseArr : Array Nat :=
  ((co3FinList 276 (by decide) pairBBase).map Fin.val).toArray

@[expose] def pairALevels : Array Level := rawLevels 276 pairAArrs pairABaseArr

@[expose] def pairBLevels : Array Level := rawLevels 276 pairBArrs pairBBaseArr

@[expose] def pairWordA0 : List Int :=
  [10, 15, 10, 7, -1, -3, 10, -1, 17, 5, 16, -9, 17, 5, 3, 2, -14, -4, -12, 17, 4, 2, 3, 2, -14,
    -4, -12, 17, 4, 2, 4, 4, 11, 2, 3, 2, -14, -4, -12, 17, 4, 2, 10, -17, -5, -10, 5, 17]

@[expose] def pairWordA1 : List Int :=
  [-17, -12, -2, -10, -2, -12, -2, -4, -17, 12, 4, 14, -2, -3, -2, -10, -2, -4, -17, 12, 4, 14, -2,
    -3, -2, -11, 3, 1, -10, -6, -5, -17, -10, -4, 17, -2, -17, -2, -16, -5, -17, 2, -10, 1, 17, 13,
    5, 2, 10]

@[expose] def pairJointArrs : Array (Array Nat) := pairAArrs ++ pairBArrs ++ co3ChainArrs

@[expose] def pairShift (l : Int) : Int := if 0 < l then l + 19 else l - 19

@[expose] def pairJointWords : Array (List Int) :=
  Array.ofFn (n := 33) fun j =>
    if j.val < 19 then []
    else if j.val = 19 then pairWordA0
    else if j.val = 20 then pairWordA1
    else (co3ChainDerivations.getD (j.val - 21) []).map pairShift

end CFSG.LocalAnalysis.WeakClosure81.SporCo3
