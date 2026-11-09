module

public import Certificates.Data.Kernel.SmithL6K
public import Certificates.Data.Kernel.SmithL6Coll
public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.SmithL6.K

open CFSG.SmithL6 CFSG.SmithL6.CollK CFSG.KC.Enum

@[expose] def imgMaskK (c M : Nat) : Nat :=
  (List.range 64).foldl (fun acc x => if M.testBit x then acc ||| 2 ^ tvA (c / 64, c % 64) x else acc) 0

@[expose] def closeRowK (T : List Nat) (c R W M : Nat) : Bool :=
  (List.range 1395).all fun i =>
    decide (fldW 11 R i < 1395) && fldW 20 W (fldW 11 R i) == apK T (fldW 20 W i) &&
      fldW 64 M (fldW 11 R i) == imgMaskK c (fldW 64 M i)

@[expose] noncomputable def fldP (w m T s : Nat) : Nat := fld(T, Nat.mul w s, m)

@[expose] noncomputable def vbit (v b : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight v b) 1) 1

@[expose] noncomputable def vpart (v b : Nat) : Nat := nIf(vbit v b, Nat.shiftLeft 1 b, 0)

@[expose] noncomputable def swpB (v b L m : Nat) : Nat :=
  nIf(vbit v b, Nat.lor (Nat.land (Nat.shiftRight m (Nat.shiftLeft 1 b)) L)
    (Nat.shiftLeft (Nat.land m L) (Nat.shiftLeft 1 b)), m)

@[expose] noncomputable def xorMask (v m : Nat) : Nat :=
  swpB v 5 0x00000000FFFFFFFF (swpB v 4 0x0000FFFF0000FFFF (swpB v 3 0x00FF00FF00FF00FF
    (swpB v 2 0x0F0F0F0F0F0F0F0F (swpB v 1 0x3333333333333333 (swpB v 0 0x5555555555555555 m)))))

@[expose] def kerMask (φ : Nat) : Nat :=
  (List.range 64).foldl (fun acc x => if !form φ x then acc ||| 2 ^ x else acc) 0

@[expose] noncomputable def imgMaskB (c K M : Nat) : Nat :=
  Nat.lor (Nat.land M K) (Nat.land (xorMask (Nat.shiftRight c 6) M) (Nat.xor K 0xFFFFFFFFFFFFFFFF))

@[expose] noncomputable def apB (T : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun c _ ih x => nIf(Nat.beq (Nat.land x 1) 1, Nat.xor c (ih (Nat.shiftRight x 1)),
      ih (Nat.shiftRight x 1))) T x

@[expose] noncomputable def rowB (T : List Nat) (c K R W M i : Nat) : Bool :=
  (fun j => bAnd(Nat.blt j 1395, bAnd(Nat.beq (fldP 20 1048575 W j) (apB T (fldP 20 1048575 W i)),
    Nat.beq (fldP 64 0xFFFFFFFFFFFFFFFF M j) (imgMaskB c K (fldP 64 0xFFFFFFFFFFFFFFFF M i)))))
    (fldP 11 2047 R i)

@[expose] noncomputable def closeRowB (T : List Nat) (c R W M : Nat) : Bool :=
  allN 1395 (rowB T c (kerMask (c % 64)) R W M)

end CFSG.SmithL6.K
