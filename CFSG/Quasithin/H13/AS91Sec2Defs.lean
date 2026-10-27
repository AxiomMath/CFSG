module

public import Mathlib.Algebra.Order.Antidiag.Prod
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.Quasithin.H13.AS91.Sp4

open Finset

variable {W : Type*} [Zero W] [Add W] [Fintype W] [DecidableEq W] (b : W → W → ZMod 2)

@[expose] def points : Finset W := univ.filter (· ≠ 0)

@[expose] def disc (x : W) : Finset W := (points (W := W)).filter fun y => y ≠ x ∧ b x y = 0

@[expose] def ovals : Finset (Finset W) :=
  ((points (W := W)).powersetCard 5).filter fun O => ∀ u ∈ O, ∀ v ∈ O, u ≠ v → b u v ≠ 0

@[expose] def singLines : Finset (Finset W) :=
  ((points (W := W) ×ˢ points).filter fun p => p.1 ≠ p.2 ∧ b p.1 p.2 = 0).image
    fun p => {p.1, p.2, p.1 + p.2}

@[expose] def spreads : Finset (Finset (Finset W)) :=
  ((singLines b).powersetCard 5).filter fun S => ∀ l ∈ S, ∀ m ∈ S, l ≠ m → Disjoint l m

@[expose] def discL (l : Finset W) : Finset (Finset W) :=
  (singLines b).filter fun m => m ≠ l ∧ ¬ Disjoint m l

@[expose] def pencil (p : W) : Finset (Finset W) := (singLines b).filter (p ∈ ·)

@[expose] def ovalsMeeting (S : Finset W) : Finset (Finset W) :=
  (ovals b).filter fun O => ¬ Disjoint O S

@[expose] def spreadsMeeting (S : Finset (Finset W)) : Finset (Finset (Finset W)) :=
  (spreads b).filter fun O => ¬ Disjoint O S

@[expose] def Stmt2_1_1 : Prop :=
  (∀ p ∈ points (W := W), ((ovals b).filter (p ∈ ·)).card = 2) ∧
    ∀ O ∈ ovals b, ∀ O' ∈ ovals b, O ≠ O' → (O ∩ O').card = 1

@[expose] def Stmt2_1_2 : Prop :=
  ∀ O ∈ ovals b, ∀ l ∈ singLines b, (O ∩ l).card = 1

@[expose] def Stmt2_2 : Prop :=
  ∀ S ∈ (points (W := W)).powerset, S.Nonempty →
    (∀ O ∈ ovals b, ¬ Disjoint O S → (O ∩ S).card = 3) →
      (∃ x ∈ points (W := W), S = disc b x ∧ S.card = 6 ∧ (ovalsMeeting b S).card = 4) ∨
        S.card = 9

@[expose] def Stmt2_1_1Dual : Prop :=
  (∀ l ∈ singLines b, ((spreads b).filter (l ∈ ·)).card = 2) ∧
    ∀ O ∈ spreads b, ∀ O' ∈ spreads b, O ≠ O' → (O ∩ O').card = 1

@[expose] def Stmt2_1_2Dual : Prop :=
  ∀ O ∈ spreads b, ∀ p ∈ points (W := W), (O ∩ pencil b p).card = 1

@[expose] def Stmt2_2Dual : Prop :=
  ∀ S ∈ (singLines b).powerset, S.Nonempty →
    (∀ O ∈ spreads b, ¬ Disjoint O S → (O ∩ S).card = 3) →
      (∃ l ∈ singLines b, S = discL b l ∧ S.card = 6 ∧ (spreadsMeeting b S).card = 4) ∨
        S.card = 9

@[expose] def Counts : Prop :=
  (points (W := W)).card = 15 ∧ (singLines b).card = 15 ∧ (ovals b).card = 6 ∧
    (spreads b).card = 6 ∧ (∀ l ∈ singLines b, l ⊆ points ∧ l.card = 3) ∧
    (∀ x ∈ points (W := W), (disc b x).card = 6 ∧ (pencil b x).card = 3) ∧
    ∀ l ∈ singLines b, (discL b l).card = 6

@[expose] def DiscChar : Prop :=
  ∀ x ∈ points (W := W), ∀ y ∈ points (W := W), x ≠ y →
    (b x y = 0 ↔ ∀ O ∈ ovals b, ¬ (x ∈ O ∧ y ∈ O))

@[expose] def DiscCharDual : Prop :=
  ∀ l ∈ singLines b, ∀ m ∈ singLines b, l ≠ m →
    (¬ Disjoint l m ↔ ∀ O ∈ spreads b, ¬ (l ∈ O ∧ m ∈ O))

instance : Decidable (DiscChar b) := by unfold DiscChar; infer_instance
instance : Decidable (DiscCharDual b) := by unfold DiscCharDual; infer_instance
instance : Decidable (Stmt2_1_1 b) := by unfold Stmt2_1_1; infer_instance
instance : Decidable (Stmt2_1_2 b) := by unfold Stmt2_1_2; infer_instance
instance : Decidable (Stmt2_2 b) := by unfold Stmt2_2; infer_instance
instance : Decidable (Stmt2_1_1Dual b) := by unfold Stmt2_1_1Dual; infer_instance
instance : Decidable (Stmt2_1_2Dual b) := by unfold Stmt2_1_2Dual; infer_instance
instance : Decidable (Stmt2_2Dual b) := by unfold Stmt2_2Dual; infer_instance
instance : Decidable (Counts b) := by unfold Counts; infer_instance

end CFSG.Quasithin.H13.AS91.Sp4
