module

public import Certificates.Data.Kernel.O8.SBCenL

public section

namespace CFSG.KC.SBCenU

open CFSG.KC.Enum CFSG.KC.SBCen CFSG.KC.SBCenL

@[expose] noncomputable def lowCntV (AR MR : Nat → Nat) (A M g Z q v : Nat) : Nat :=
  strictN (Nat.shiftRight q 7) fun h => strictN (Nat.land q 127) fun e' =>
  strictN (Nat.shiftRight v 7) fun vg => strictN (Nat.land v 127) fun ve =>
    nIf(Nat.beq fld(M, Nat.mul 9 vg, 511) fld(MR h, Nat.mul 9 g, 511),
      pop (Nat.land Z (zl (Nat.xor (Nat.xor IDX (AR h)) (Nat.mul (Nat.xor e' fld(A, Nat.mul 7 ve, 127)) RU)))),
      0)

@[expose] noncomputable def qWalkU (AR MR F : Nat → Nat) (A M g Z : Nat) (Q : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun q _ ih => Nat.add
    (nIf(Nat.blt q 65536, lowCntV AR MR A M g Z q (F q), 0)) (Nat.shiftLeft ih 20)) Q

@[expose] noncomputable def uWalkU (AR MR F : Nat → Nat) (A M g Z : Nat) (U : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun u _ ih => Nat.add
    (lowCntV AR MR A M g Z u (F u)) (Nat.shiftLeft ih 20)) U

@[expose] noncomputable def grpU (mul : Nat → Nat → Nat) (AR MR F : Nat → Nat) (z : Nat) (Q U : List Nat)
    (nQ g : Nat) : Nat :=
  strictN (lanesK (fun e => strictN (Nat.add e (Nat.mul 128 g)) fun a => strictN (F a) fun u =>
    strictN (mul (mul a u) z) fun s => nIf(Nat.beq s 0, 64, 0)) 128) fun Zi =>
  strictN (lanesK (fun e => strictN (Nat.add e (Nat.mul 128 g)) fun a => strictN (F a) fun u =>
    strictN (mul (mul a u) z) fun s => nIf(Nat.beq s 0, 0, nIf(Nat.beq (mul s s) 0, 64, 0))) 128) fun Zo =>
  strictN (AR g) fun A => strictN (MR g) fun M =>
  Nat.add (pop Zi) (Nat.add (Nat.shiftLeft (qWalkU AR MR F A M g Zi Q) 20)
    (Nat.add (Nat.shiftLeft (cuSum (extMulF 65536 mul F z) (Nat.add g 512) Zi Q) 20)
      (Nat.shiftLeft (uWalkU AR MR F A M g Zo U) (Nat.mul 20 (Nat.succ nQ)))))

@[expose] noncomputable def blkU (mul : Nat → Nat → Nat) (AR MR F : Nat → Nat) (z : Nat) (Q U : List Nat)
    (nQ t : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun j ih => Nat.add (grpU mul AR MR F z Q U nQ (Nat.add (Nat.mul 64 t) j)) ih) 64

@[expose] noncomputable def conjB (mul : Nat → Nat → Nat) (F : Nat → Nat) (z a n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i ih => bAnd(
    strictB (Nat.add a i) fun y => strictB (F y) fun u => strictB (F u) fun v =>
      Nat.beq (mul z y) (mul v z), ih)) n

end CFSG.KC.SBCenU

end
