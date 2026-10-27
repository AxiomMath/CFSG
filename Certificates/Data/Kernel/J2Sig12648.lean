module

public import Certificates.Data.Kernel.ConjRec

public section

namespace CFSG.KC.J2Sig

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.ConjRec

@[expose] noncomputable def m9 (p q : Nat) : Nat := pcomp (nat_lit 315) (nat_lit 9) (mask (nat_lit 9)) p q

@[expose] noncomputable def p4 (I c : Nat) : Bool :=
  strictB (m9 c c) fun c2 => Nat.beq (m9 c2 c2) I

@[expose] noncomputable def p40 (I g : Nat) : Bool :=
  strictB (m9 g g) fun g2 => strictB (m9 g2 g2) fun g4 => strictB (m9 g4 g) fun g5 =>
    strictB (m9 g5 g5) fun g10 => strictB (m9 g10 g10) fun g20 => Nat.beq (m9 g20 g20) I

@[expose] noncomputable def inVs (V : Nat → Nat) (lo cnt g : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) false
    (fun j ih => bIf(Nat.beq g (V (Nat.add lo j)), true, ih)) cnt

@[expose] noncomputable def wst (L0 L1 L2 a d : Nat) : Nat :=
  nIf(Nat.beq d (nat_lit 0), a, nIf(Nat.beq d (nat_lit 1), m9 a L0,
    nIf(Nat.beq d (nat_lit 2), m9 a L1, m9 a L2)))

@[expose] noncomputable def wval (L0 L1 L2 I c : Nat) : Nat :=
  strictN (wst L0 L1 L2 I (fldO c (nat_lit 0) (nat_lit 2))) fun a1 =>
    strictN (wst L0 L1 L2 a1 (fldO c (nat_lit 2) (nat_lit 2))) fun a2 =>
      strictN (wst L0 L1 L2 a2 (fldO c (nat_lit 4) (nat_lit 2))) fun a3 =>
        wst L0 L1 L2 a3 (fldO c (nat_lit 6) (nat_lit 2))

@[expose] noncomputable def witK (X XI X2 X2I I c g : Nat) : Bool :=
  strictB (wval g (m9 X (m9 g XI)) (m9 X2 (m9 g X2I)) I c) fun v =>
    bAnd(Nat.beq (m9 v (m9 v v)) I, bIf(Nat.beq v I, false, true))

@[expose] noncomputable def zK (X XI X2 X2I I : Nat) (V : Nat → Nat) (W k g : Nat) : Bool :=
  bIf(p40 I g, bIf(Nat.beq g I, true, bIf(inVs V (nat_lit 9) (nat_lit 9) g, true,
    witK X XI X2 X2I I (fldO W (Nat.mul (nat_lit 8) k) (nat_lit 8)) g)), true)

@[expose] noncomputable def wK (I G GI : Nat) (V : Nat → Nat) (lo c : Nat) : Bool :=
  bIf(p4 I c, strictB (m9 G (m9 c GI)) fun h =>
    bIf(Nat.beq h I, true, inVs V lo (nat_lit 3) h), true)

end CFSG.KC.J2Sig
