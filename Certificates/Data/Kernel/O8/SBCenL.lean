module

public import Certificates.Data.Kernel.O8.SBCen

public section

namespace CFSG.KC.SBCenL

open CFSG.KC.Enum CFSG.KC.SBCen

@[expose] noncomputable def lanesK (f : Nat → Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun e ih => Nat.add ih (Nat.shiftLeft (f e) (Nat.mul 7 e))) n

@[expose] noncomputable def IDX : Nat := lanesK (fun e => e) 128

@[expose] noncomputable def RU : Nat := lanesK (fun _ => 1) 128

@[expose] noncomputable def HM : Nat := lanesK (fun _ => 64) 128

@[expose] noncomputable def LM : Nat := lanesK (fun _ => 63) 128

@[expose] noncomputable def zl (X : Nat) : Nat :=
  strictN X fun X => Nat.xor HM (Nat.land HM (Nat.lor (Nat.add (Nat.land X LM) LM) X))

@[expose] noncomputable def pop (Z : Nat) : Nat :=
  strictN (Nat.mod (Nat.shiftRight Z 6) 16383) fun r => Nat.add (Nat.land r 127) (Nat.shiftRight r 7)

@[expose] noncomputable def lowCnt (AR MR : Nat → Nat) (A M g Z q : Nat) : Nat :=
  strictN (Nat.shiftRight q 7) fun h => strictN (Nat.land q 127) fun e' =>
    nIf(Nat.beq fld(M, Nat.mul 9 h, 511) fld(MR h, Nat.mul 9 g, 511),
      pop (Nat.land Z (zl (Nat.xor (Nat.xor IDX (AR h)) (Nat.mul (Nat.xor e' fld(A, Nat.mul 7 e', 127)) RU)))),
      0)

@[expose] noncomputable def cmU (mul : Nat → Nat → Nat) (c : Nat) (Q : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun q _ ih => Nat.add (nIf(Nat.blt q 65536, 0, nIf(Nat.beq (mul c q) (mul q c), 1, 0)))
      (Nat.shiftLeft ih 20)) Q

@[expose] noncomputable def zS0 (A g2 : Nat) : Nat := nIf(Nat.beq g2 0, zl (Nat.xor IDX A), 0)

@[expose] noncomputable def zI (g S0 : Nat) : Nat := nIf(Nat.beq g 0, Nat.xor S0 (Nat.land S0 64), S0)

@[expose] noncomputable def zO (AR MR : Nat → Nat) (A M g2 S0 : Nat) : Nat :=
  strictN fld(M, Nat.mul 9 g2, 511) fun g3 => strictN fld(MR g2, Nat.mul 9 g2, 511) fun g4 =>
    nIf(Nat.beq g4 0, strictN (zl (Nat.xor (Nat.xor IDX A) (Nat.xor (AR g2) (AR g3)))) fun Zl =>
      Nat.xor Zl (Nat.land Zl S0), 0)

@[expose] noncomputable def qWalk (AR MR : Nat → Nat) (A M g Z : Nat) (Q : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun q _ ih => Nat.add
    (nIf(Nat.blt q 65536, lowCnt AR MR A M g Z q, 0)) (Nat.shiftLeft ih 20)) Q

@[expose] noncomputable def uWalk (AR MR : Nat → Nat) (A M g Z : Nat) (U : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun u _ ih => Nat.add
    (lowCnt AR MR A M g Z u) (Nat.shiftLeft ih 20)) U

@[expose] noncomputable def cuSum (mul : Nat → Nat → Nat) (g Z : Nat) (Q : List Nat) : Nat :=
  nIf(Nat.beq Z 0, 0, Nat.rec (motive := fun _ => Nat) 0 (fun e ih => Nat.add
    (nIf(Nat.beq fld(Z, Nat.add (Nat.mul 7 e) 6, 1) 1, cmU mul (Nat.add e (Nat.mul 128 g)) Q, 0)) ih)
    128)

@[expose] noncomputable def grpT (mul : Nat → Nat → Nat) (AR MR : Nat → Nat) (Q U : List Nat)
    (nQ g A M Zi Zo : Nat) : Nat :=
  Nat.add (pop Zi) (Nat.add (Nat.shiftLeft (qWalk AR MR A M g Zi Q) 20)
    (Nat.add (Nat.shiftLeft (cuSum mul g Zi Q) 20)
      (Nat.shiftLeft (uWalk AR MR A M g Zo U) (Nat.mul 20 (Nat.succ nQ)))))

@[expose] noncomputable def grpG (mul : Nat → Nat → Nat) (AR MR : Nat → Nat) (Q U : List Nat) (nQ g : Nat) :
    Nat :=
  strictN (AR g) fun A => strictN (MR g) fun M => strictN fld(M, Nat.mul 9 g, 511) fun g2 =>
  strictN (zS0 A g2) fun S0 => strictN (zI g S0) fun Zi => strictN (zO AR MR A M g2 S0) fun Zo =>
    grpT mul AR MR Q U nQ g A M Zi Zo

@[expose] noncomputable def blkG (mul : Nat → Nat → Nat) (AR MR : Nat → Nat) (Q U : List Nat) (nQ s : Nat) :
    Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun j ih => Nat.add (grpG mul AR MR Q U nQ (Nat.add (Nat.mul 64 s) j)) ih) 64

@[expose] noncomputable def sqAt (AR MR : Nat → Nat) (g : Nat) : Bool :=
  strictB (AR g) fun A => strictB fld(MR g, Nat.mul 9 g, 511) fun g2 => strictB (AR g2) fun A2 =>
  strictB (AR fld(MR g, Nat.mul 9 g2, 511)) fun A3 =>
  Nat.rec (motive := fun _ => Bool) true (fun e ih => bAnd(Nat.beq
    fld(A2, Nat.mul 7 (Nat.xor e fld(A, Nat.mul 7 e, 127)), 127)
    (Nat.xor fld(A2, Nat.mul 7 e, 127) fld(A3, Nat.mul 7 e, 127)), ih)) 128

@[expose] noncomputable def sqBlk (AR MR : Nat → Nat) (b : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun j ih => bAnd(sqAt AR MR (Nat.add (Nat.mul 64 b) j), ih)) 64

end CFSG.KC.SBCenL

end
