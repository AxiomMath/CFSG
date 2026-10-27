module

public import Certificates.Data.Kernel.SporSch.ThRows

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum

@[expose] noncomputable def ccP : Nat :=
  Nat.div (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 63488)) (nat_lit 1))
    (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 256)) (nat_lit 1))

@[expose] noncomputable def rmP : Nat := Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 248)) (nat_lit 1)

@[expose] noncomputable def mulPk (A B : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => Nat.xor acc (Nat.land (Nat.mul (Nat.land (Nat.shiftRight A k) ccP) rmP)
      (Nat.mul (Nat.land (Nat.shiftRight B (Nat.mul k (nat_lit 256))) rmP) ccP))) (nat_lit 248)

@[expose] noncomputable def unpk (M i : Nat) : Nat :=
  Nat.land (Nat.shiftRight M (Nat.mul i (nat_lit 256))) rmP

@[expose] noncomputable def repk (R : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft (R i) (Nat.mul i (nat_lit 256)))) (nat_lit 248)

@[expose] noncomputable def letPk (A B BB : Nat) (z : Int) : Nat :=
  strictN (CFSG.KS.Mathieu.icode z) (fun c => nIf(Nat.beq c (nat_lit 2), A,
    nIf(Nat.beq c (nat_lit 3), A, nIf(Nat.beq c (nat_lit 4), B, BB))))

@[expose] noncomputable def wordR (A B BB : Nat) (w : List Int) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun z t ih => List.rec (motive := fun _ => Nat) (letPk A B BB z)
      (fun _ _ _ => mulPk (letPk A B BB z) ih) t) w

@[expose] noncomputable def parPk (EDG : Nat → Nat) (i p l : Nat) : Bool :=
  bAnd(Nat.blt p i, bAnd(bIf(Nat.beq l (nat_lit 1), true, Nat.beq l (nat_lit 2)),
    Nat.beq (EDG (Nat.add (Nat.add p p) (Nat.sub l (nat_lit 1)))) i))

@[expose] noncomputable def edgK (S SG : Nat → Nat) (X Y YY m e1 e2 : Nat) : Bool :=
  bAnd(Nat.blt e1 (nat_lit 819), bAnd(Nat.blt e2 (nat_lit 819),
    bAnd(Nat.beq (mulPk (mulPk X m) X) (S (SG e1)), Nat.beq (mulPk (mulPk Y m) YY) (S (SG e2)))))

@[expose] noncomputable def entK (S SG TU PAR LAB EDG : Nat → Nat) (T X Y YY i : Nat) : Bool :=
  strictB (SG i) (fun g => bAnd(Nat.blt g (nat_lit 819), bAnd(Nat.beq (TU g) i,
    bAnd(bIf(Nat.beq i (nat_lit 0), Nat.beq (S g) T, parPk EDG i (PAR i) (LAB i)),
      edgK S SG X Y YY (S g) (EDG (Nat.add i i)) (EDG (Nat.succ (Nat.add i i)))))))

@[expose] noncomputable def srtK (S : Nat → Nat) (k : Nat) : Bool :=
  bAnd(Nat.beq (repk (unpk (S k))) (S k),
    bIf(Nat.blt k (nat_lit 818), Nat.blt (S k) (S (Nat.succ k)), true))

end CFSG.KS.SporSch

end
