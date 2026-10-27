module

public import Certificates.Data.Kernel.L34W.Fix

public section

namespace CFSG.KC.L34W

open CFSG.KC.Enum CFSG.KS
open CFSG.ComponentClassification.GrSLit.L34Facts.Real.WIso

@[expose] noncomputable def addIx (a b : Nat) : Nat :=
  Nat.add (Nat.mul (nat_lit 4) (Nat.mod (Nat.add (Nat.div a (nat_lit 4)) (Nat.div b (nat_lit 4))) (nat_lit 4)))
    (Nat.mod (Nat.add (Nat.mod a (nat_lit 4)) (Nat.mod b (nat_lit 4))) (nat_lit 4))

@[expose] noncomputable def isSubM (m : Nat) : Bool :=
  bAnd(hasBit m (nat_lit 0),
    allN (nat_lit 16) fun a => bIf(hasBit m a,
      allN (nat_lit 16) fun b => bIf(hasBit m b, hasBit m (addIx a b), true), true))

@[expose] noncomputable def inL (L : List Nat) (m : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun x _ ih => bIf(Nat.beq m x, true, ih)) L

@[expose] noncomputable def kcR (L : List Nat) (lo n : Nat) : Bool :=
  allN n fun r => strictB (Nat.add lo r) fun m => bIf(isSubM m, inL L m, true)

@[expose] noncomputable def rhoK (G : Nat → Nat) (lab : Nat) : Nat :=
  nIf(Nat.beq lab (nat_lit 0), G (nat_lit 4),
    nIf(Nat.beq lab (nat_lit 1), G (nat_lit 5), pcomp (nat_lit 42) (nat_lit 6) (mask 6) (G (nat_lit 4)) (G (nat_lit 5))))

@[expose] noncomputable def cjE (G Y : Nat → Nat) (t i lab t' j : Nat) : Bool :=
  bAnd(bAnd(Nat.blt lab (nat_lit 3), bAnd(Nat.blt t' (nat_lit 64), Nat.blt j (nat_lit 36))),
    bAnd(bAnd(Nat.blt t (nat_lit 64), Nat.blt i (nat_lit 36)),
      strictB (Y (Nat.add (Nat.mul (nat_lit 64) j) t')) fun c =>
        Nat.beq (pcomp (nat_lit 42) (nat_lit 6) (mask 6) c (Y (Nat.add (Nat.mul (nat_lit 64) i) t)))
          (pcomp (nat_lit 42) (nat_lit 6) (mask 6) (rhoK G lab) c)))

@[expose] noncomputable def cjOK (G Y : Nat → Nat) (L : List ((ℕ × ℕ) × ℕ × ℕ × ℕ)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun e _ ih => bAnd(cjE G Y e.1.1 e.1.2 e.2.1 e.2.2.1 e.2.2.2, ih)) L

@[expose] noncomputable def toOK (TY : Nat → Nat) : Bool :=
  allN (nat_lit 144) fun j => Nat.blt (TY j) (nat_lit 3)

@[expose] noncomputable def tpOK (OT CM TY : Nat → Nat) : Bool :=
  allN (nat_lit 144) fun j => strictB (CM j) fun c => strictB (Nat.div (OT j) (nat_lit 64)) fun i =>
    strictB (TY j) fun ty => allN (nat_lit 144) fun j' => bIf(hasBit c j',
      bIf(Nat.beq i (Nat.div (OT j') (nat_lit 64)), true, bNot (Nat.beq ty (TY j'))), true)

@[expose] noncomputable def someN (n : Nat) (f : Nat → Bool) : Bool := bNot (allN n fun x => bNot (f x))

@[expose] noncomputable def fsZ (T A : Nat → Nat) (b i z : Nat) : Bool :=
  bIf(fixC A b i (nat_lit 1) z,
    someN (nat_lit 1024) fun x => bAnd(fixC A b i (nat_lit 1) x, eqC (nat_lit 1) (mulC T x x) z), true)

@[expose] noncomputable def fsOK (T A OT BT TY : Nat → Nat) : Bool :=
  allN (nat_lit 144) fun j => bIf(Nat.beq (TY j) (nat_lit 0),
    strictB (BT j) fun b => strictB (Nat.div (OT j) (nat_lit 64)) fun i =>
      bAnd(fsZ T A b i (nat_lit 8), bAnd(fsZ T A b i (nat_lit 2), fsZ T A b i (nat_lit 10))), true)

end CFSG.KC.L34W

end
