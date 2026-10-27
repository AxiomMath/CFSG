module

public import CFSG.RankThree.Native.Co3FiveData
public import CFSG.RankThree.Native.PermEnumeration

public section

namespace CFSG.RankThree.Native

open CFSG.Monster.B.Co2.Native

@[expose] def co3FiveX0Arr : Array Nat := co3FiveArr 0

@[expose] def co3FiveX25Arr : Array Nat := co3FiveArr 1

@[expose] def co3FiveQGenArrs : Array (Array Nat) := #[co3FiveArr 2, co3FiveArr 3]

@[expose] def co3FiveAGenArrs : Array (Array Nat) := #[co3FiveArr 2, co3FiveArr 3]

@[expose] def co3FiveC25GenArrs : Array (Array Nat) :=
  #[co3FiveArr 2, co3FiveArr 3, co3FiveArr 4, co3FiveArr 5]

@[expose] def co3FiveC0GenArrs : Array (Array Nat) := #[co3FiveX0Arr, co3FiveArr 6, co3FiveArr 7]

@[expose] def co3FiveDGenArrs : Array (Array Nat) :=
  #[commutatorA 276 co3FiveC0GenArrs[1]! co3FiveC0GenArrs[2]!, co3FiveC0GenArrs[2]!]

@[expose] def co3FiveGArr : Array Nat := co3FiveArr 8

@[expose] def co3FiveKArr : Array Nat := co3FiveArr 9

@[expose] def co3FiveHArr (j : Nat) : Array Nat :=
  if j = 0 ∨ j = 25 then idA 276 else if j < 25 then co3FiveArr (j + 10) else co3FiveArr (j + 9)

@[expose] def co3FiveLineArr (j : Nat) : Array Nat :=
  if j = 0 then co3FiveX0Arr else if j = 25 then co3FiveX25Arr
  else conjA 276 (co3FiveHArr j) co3FiveX0Arr

@[expose] def co3FiveTArr : Array Nat := co3FiveArr 10

@[expose] def co3FiveZArr : Array Nat := conjA 276 co3FiveTArr co3FiveX0Arr

@[expose] def co3FiveKeyPts : List Nat := [0, 1, 2, 3, 4, 5, 6]

end CFSG.RankThree.Native
