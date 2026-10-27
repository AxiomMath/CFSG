module

public import CFSG.RankThree.Native.Fi22FiveData
public import CFSG.Monster.B.Fischer.Fi22OuterArrays
public import CFSG.RankThree.Native.PermEnumeration
public import CFSG.Monster.B.Fischer.Fi22OrderCheckInputs

public section

namespace CFSG.RankThree.Native

open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer

@[expose] def fi22FiveQ1Arr : Array Nat := fi22FiveArr 0

@[expose] def fi22FiveQ2Arr : Array Nat := fi22FiveArr 1

@[expose] def fi22FiveQGenArrs : Array (Array Nat) := #[fi22FiveQ1Arr, fi22FiveQ2Arr]

@[expose] def fi22FiveWArr : Array Nat := fi22FiveArr 2

@[expose] def fi22FiveAArr : Array Nat := fi22OuterArr3510 1

@[expose] def fi22FiveLineArr (i : Nat) : Array Nat :=
  if i = 0 then fi22FiveQ1Arr else if i = 1 then fi22FiveQ2Arr
  else compA 3510 fi22FiveQ1Arr (powA 3510 fi22FiveQ2Arr (i - 1))

@[expose] def fi22FiveHArr (i : Nat) : Array Nat :=
  if i = 0 then idA 3510 else fi22FiveArr (i + 2)

@[expose] def fi22FiveCGenArrs (i : Nat) : Array (Array Nat) :=
  #[fi22FiveLineArr i, conjInvA 3510 (fi22FiveHArr i) fi22FiveAArr,
    conjInvA 3510 (fi22FiveHArr i) fi22FiveQ2Arr, fi22FiveWArr]

@[expose] def fi22FiveDGenArrs (i : Nat) : Array (Array Nat) :=
  #[commutatorA 3510 (fi22FiveCGenArrs i)[1]! (fi22FiveCGenArrs i)[2]!, (fi22FiveCGenArrs i)[2]!]

@[expose] def fi22FiveKeyPts : List Nat := [0, 1, 2, 3, 6, 4]

end CFSG.RankThree.Native
