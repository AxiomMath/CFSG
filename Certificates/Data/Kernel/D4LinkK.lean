module

public import CFSG.Certificates.Kernel.Enum.Defs
public import CFSG.Certificates.Kernel.Lie.CT.Core
public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KC.D4Link

open CFSG.KC.Enum CFSG.KS
open CFSG.KLie.CT (fget)

@[expose] noncomputable def mulTab : Nat :=
  2821848294356612419217921029917578219971947684264937521152

@[expose] noncomputable def mulK (a b : Nat) : Nat :=
  pg 3 (mask 3) mulTab (Nat.add (Nat.mul 8 a) b)

@[expose] noncomputable def invTab : Nat := 9272648

@[expose] noncomputable def invK (c : Nat) : Nat := pg 3 (mask 3) invTab c

@[expose] noncomputable def vget (V j : Nat) : Nat := pg 3 (mask 3) V j

@[expose] noncomputable def dotK (M V i : Nat) : Nat :=
  mulK (vget M (8 * i)) (vget V 0) ^^^ mulK (vget M (8 * i + 1)) (vget V 1) ^^^
    mulK (vget M (8 * i + 2)) (vget V 2) ^^^ mulK (vget M (8 * i + 3)) (vget V 3) ^^^
    mulK (vget M (8 * i + 4)) (vget V 4) ^^^ mulK (vget M (8 * i + 5)) (vget V 5) ^^^
    mulK (vget M (8 * i + 6)) (vget V 6) ^^^ mulK (vget M (8 * i + 7)) (vget V 7)

@[expose] def leadF (f : Nat → Nat) : Nat :=
  match (List.finRange 8).find? (fun i => decide (f i.val ≠ 0)) with
  | some i => f i.val
  | none => 1

@[expose] def nzF (f : Nat → Nat) : Bool := (List.finRange 8).any fun i => f i.val != 0

@[expose] noncomputable def mvK (M V : Nat) : Nat := pmk 8 3 (dotK M V)

@[expose] noncomputable def normK (W : Nat) : Nat :=
  strictN (invK (leadF (vget W))) fun g => pmk 8 3 fun i => mulK g (vget W i)

@[expose] noncomputable def actK (GM : Nat → Nat) (k V : Nat) : Nat :=
  strictN (mvK (GM k) V) normK

@[expose] noncomputable def validK (V : Nat) : Bool := nzF (vget V) && leadF (vget V) == 1

@[expose] noncomputable def kstep (a x : Nat) : Nat := Nat.add (Nat.mul a 8) x

@[expose] noncomputable def keyK (V : Nat) : Nat :=
  kstep (kstep (kstep (kstep (kstep (kstep (kstep (kstep 0 (vget V 0)) (vget V 1)) (vget V 2))
    (vget V 3)) (vget V 4)) (vget V 5)) (vget V 6)) (vget V 7)

@[expose] noncomputable def genStepV (actK : Nat → Nat → Nat) (V : Nat → Nat) (t row k c : Nat) :
    Nat :=
  nIf(Nat.beq c (nat_lit 0), nat_lit 0,
    strictN (actK k t) fun y => strictN (fget row k (nat_lit 12)) fun j =>
      nIf(Nat.blt j c, nIf(Nat.beq (V j) y, c, nat_lit 0),
        nIf(Nat.beq j c, nIf(Nat.beq (V c) y, Nat.succ c, nat_lit 0), nat_lit 0)))

@[expose] noncomputable def pointStepV (actK : Nat → Nat → Nat) (ng : Nat) (V E : Nat → Nat)
    (i c : Nat) : Nat :=
  strictN (V i) fun t => strictN (E i) fun row =>
    Nat.rec (motive := fun _ => Nat → Nat) (fun c => c)
      (fun r ih c => strictN (genStepV actK V t row (Nat.sub (Nat.sub ng r) (nat_lit 1)) c) ih)
      ng c

@[expose] noncomputable def runFV (actK : Nat → Nat → Nat) (ng : Nat) (V E : Nat → Nat)
    (len : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ c => c)
    (fun _ ih lo c => strictN (nIf(Nat.blt lo c, pointStepV actK ng V E lo c, nat_lit 0))
      (ih (Nat.succ lo))) len

@[expose] noncomputable def runSlV (actK : Nat → Nat → Nat) (ng : Nat) (V E : Nat → Nat)
    (L : Nat) (C : Nat → Nat) (s : Nat) : Bool :=
  Nat.beq (runFV actK ng V E L (Nat.mul L s) (C s)) (C (Nat.succ s))

end CFSG.KC.D4Link

end
