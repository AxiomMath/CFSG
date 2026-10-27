module

public import Certificates.Data.Kernel.SmithL6K
public import Certificates.Data.Kernel.SmithL6Coll

public section

namespace CFSG.SmithL6.K

open CFSG.SmithL6 CFSG.SmithL6.CollK

@[expose] def imgMaskK (c M : Nat) : Nat :=
  (List.range 64).foldl (fun acc x => if M.testBit x then acc ||| 2 ^ tvA (c / 64, c % 64) x else acc) 0

@[expose] def closeRowK (T : List Nat) (c R W M : Nat) : Bool :=
  (List.range 1395).all fun i =>
    decide (fldW 11 R i < 1395) && fldW 20 W (fldW 11 R i) == apK T (fldW 20 W i) &&
      fldW 64 M (fldW 11 R i) == imgMaskK c (fldW 64 M i)

end CFSG.SmithL6.K
