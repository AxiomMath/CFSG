module

public section

namespace CFSG.Sporadic.He.Native

@[expose] def seedA : String := include_str "../../../../CFSG/Blueprint/Data/HeG1-f7r50B0.m1"

@[expose] def seedB : String := include_str "../../../../CFSG/Blueprint/Data/HeG1-f7r50B0.m2"

@[expose] def rootDigits : String :=
  "56506402656241642610606054444550603664015453444221"

@[expose] def rootVec (_ : Unit := ()) : Array Nat := rootDigits.toList.toArray.map fun c => c.toNat - '0'.toNat

@[expose] def chainBase : Array Nat := #[0, 1, 3, 4, 2]

@[expose] def chainQ (_ : Unit := ()) : Array Nat := Array.range 50

@[expose] def chainQb (_ : Unit := ()) : Array Nat := #[0, 1, 3, 4, 2]

@[expose] def chainWords (_ : Unit := ()) : Array (List Int) := #[
    [1],
    [2],
    [4, -3, 4, -3, 4, -3, -4, 4, 4, 3, -4, -3, -4, -3, -4, -3, -4, -3, -3],
    [4, 4, -5, 4, -5, 4, 4, -5, 4, 4, -3, -3, -3, 4, 4, -3, -3, -3, -3, -3, 4, 3, 4, 4, 3, 4, 3, 4,
      4, 4, -3, -4, -4],
    [-5, -6, -6, -5, 6, -5, 6, 6, -5, -4, -4, -6, 4, -6, -4, 4, 3, 3, -4, 3, -4, -3, 4, 3, 4, 4, 3],
    [-6, -6, -5, -7, -5, 6, -4, 6, -4, -4, -5, 4, 4, -3, 4, 4, 3, 4, 4, -3],
    [-6, -3, -7, -6, -7, 6, -4, -6, -4, -3, 6, -7, -3, -4, -3, -4, -3, -4, -4, -4, -3, -4],
    [-7, -8, 6, -3, -8, 9, 4, 9, -6, -9, -3, -3, -3, 4, 3, -4, -3, 4, -3, -4, -3, -3, -4, -3, 4, -3,
      -4, -3]]

@[expose] def subRoots : Array Nat := #[0, 1, 6, 21, 24, 33, 368]

@[expose] def subSizes : List Nat := [1, 4480, 1344, 840, 840, 720, 105]

@[expose] def witWord (_ : Unit := ()) : List Int := [2, 1, -2, 1, 2]

end CFSG.Sporadic.He.Native
