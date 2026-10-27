module

public import Certificates.Data.GH74.McLSylowThree

public section

namespace CFSG.Sporadic.Recognition.McLAS

open CFSG.Sporadic.Th.Native

@[expose] def wtIdx : Array Nat := #[1, 11, 35, 77, 6, 4]

@[expose] def wtElem (i : Nat) : Table := sylTwoEnum[wtIdx[i]!]!

@[expose] def wtLetterT (z : Int) : Table :=
  if 0 < z then wtElem (z.natAbs - 1) else invT 275 (wtElem (z.natAbs - 1))

@[expose] def wtRels : List (List Int × List Int) := [
  ([1, 1], []),
  ([2, 2], []),
  ([3, 3], []),
  ([4, 4], []),
  ([2, 3], [3, 2]),
  ([2, 4], [4, 2]),
  ([2, 1], [1, 2]),
  ([3, 4], [4, 3]),
  ([3, 1], [1, 3]),
  ([4, 1], [1, 4]),
  ([1, 5], [5, 1]),
  ([1, 6], [6, 1]),
  ([5, 2], [2, 1, 5]),
  ([5, 3], [4, 1, 5]),
  ([5, 4], [3, 1, 5]),
  ([-5, 2], [2, 1, -5]),
  ([-5, 3], [4, 1, -5]),
  ([-5, 4], [3, 1, -5]),
  ([6, 2], [2, 6]),
  ([6, 3], [3, 1, 6]),
  ([6, 4], [2, 4, 1, 6]),
  ([-6, 2], [2, -6]),
  ([-6, 3], [3, 1, -6]),
  ([-6, 4], [2, 4, 1, -6]),
  ([5, 5], [1]),
  ([6, 6], [1]),
  ([5, 6, 5, 6, 5, 6, 5, 6], [1])
]

@[expose] def wtNe : List (List Int × List Int × Nat) := [([1], [], 1)]

@[expose] def wtCheck : Bool :=
  wtIdx.size == 6 && allIn 0 6 (fun i => decide (wtIdx[i]! < sylTwoEnum.size)) &&
    allIn 0 6 (fun i => invOK 275 (wtElem i) (invT 275 (wtElem i))) &&
    wtRels.all (fun r => wordT 275 wtLetterT r.1 == wordT 275 wtLetterT r.2) &&
    wtNe.all (fun r => decide (r.2.2 < 275) &&
      ap (wordT 275 wtLetterT r.1) r.2.2 != ap (wordT 275 wtLetterT r.2.1) r.2.2)

@[expose] def wtCertificate (_ : Unit) : Bool := wtCheck

end CFSG.Sporadic.Recognition.McLAS
