module

public import CFSG.RankThree.Native.Co2FiveData
public import CFSG.RankThree.Native.PermEnumeration

public section

namespace CFSG.RankThree.Native

open CFSG.Monster.B.Co2.Native

@[expose] def co2FiveX0Arr : Array Nat := co2FiveArr 0

@[expose] def co2FiveX1Arr : Array Nat := co2FiveArr 1

@[expose] def co2FiveC0GenArrs : Array (Array Nat) := #[co2FiveArr 2, co2FiveArr 3]

@[expose] def co2FiveQGenArrs : Array (Array Nat) := #[co2FiveArr 4, co2FiveArr 5]

@[expose] def co2FiveAGenArrs : Array (Array Nat) := #[co2FiveArr 4, co2FiveArr 5]

@[expose] def co2FiveC1GenArrs : Array (Array Nat) := #[co2FiveX1Arr, co2FiveArr 6, co2FiveArr 7]

@[expose] def co2FiveDGenArrs : Array (Array Nat) :=
  #[commutatorA 2300 co2FiveC1GenArrs[1]! co2FiveC1GenArrs[2]!, co2FiveC1GenArrs[2]!]

@[expose] def co2FiveHArr (j : Nat) : Array Nat :=
  if j ≤ 1 then idA 2300 else co2FiveArr (j + 7)

@[expose] def co2FiveLineArr (j : Nat) : Array Nat :=
  if j = 0 then co2FiveX0Arr else if j = 1 then co2FiveX1Arr
  else conjA 2300 (co2FiveHArr j) co2FiveX1Arr

@[expose] def co2FiveTArr : Array Nat := co2FiveArr 8

@[expose] def co2FiveZArr : Array Nat := conjA 2300 co2FiveTArr co2FiveX1Arr

@[expose] def co2FiveKeyPts : List Nat := [0, 1, 2, 3, 5, 4]

end CFSG.RankThree.Native
