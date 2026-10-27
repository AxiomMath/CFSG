module

public import CFSG.RankThree.GF2n.Stroth80.Sec12Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

structure Sec7Hyp (hc : Ctx M Q Z B) (n : ℕ) (t : G) : Prop where
  toSec5 : Sec5Hyp hc n t
  notPlus4 : ¬ OmegaPlusNat hc t 2
  orth : ∃ m : ℕ, 2 ≤ m ∧ (OmegaPlusNat hc t m ∨ OmegaMinusNat hc t m)
  large : Nat.card Q * Nat.card Z < Nat.card ↥(hc.CN t)

@[expose] def ConjMod (M Q : Subgroup G) (t x : G) : Prop :=
  x ∈ M ∧ ∃ g ∈ M, x * (g * t * g⁻¹)⁻¹ ∈ Q

structure Sec7A (hc : Ctx M Q Z B) (t r : G) : Prop where
  mem : r ∈ Rt M (LB M Q B) t
  plane : HypPlane Q Z B (conjSubgroup r B) t
  gen : Rt M (LB M Q B) t = LB M Q B ⊔ LB M Q (conjSubgroup r B)

@[expose] def Fgen (M Q L Z0 : Subgroup G) : Subgroup G :=
  Subgroup.closure {x : G | x ∈ L ∧ ∃ s ∈ Z0, ConjMod M Q s x}

@[expose] def Conc71a (hc : Ctx M Q Z B) (t : G) : Prop :=
  ∃ s ∈ Rt M (LB M Q B) t, (∀ r ∈ Rt M (LB M Q B) t, ⁅s, r⁆ ∈ Q) ∧
    ∃ g ∈ M, g * s * g⁻¹ ∈ LB M Q B ∧ g * s * g⁻¹ ∉ hc.CN t

@[expose] def Conc71b (hc : Ctx M Q Z B) (n : ℕ) (t : G) : Prop :=
  OmegaMinusNat hc t 3 ∧ n = 10

@[expose] def Conc71c (hc : Ctx M Q Z B) (n : ℕ) (t : G) : Prop :=
  OmegaPlusNat hc t 3 ∧ n = 10

@[expose] def Conc71d (hc : Ctx M Q Z B) (n : ℕ) (t : G) : Prop :=
  OmegaPlusNat hc t 4 ∧ n = 12

@[expose] def Conc71e (hc : Ctx M Q Z B) (t : G) : Prop :=
  (OmegaMinusNat hc t 2 ∨ OmegaPlusNat hc t 3 ∨ OmegaPlusNat hc t 4) ∧
  (∃ x, ConjMod M Q t x ∧ ⁅x, t⁆ ∈ Q ∧
      ∃ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅x, w⁆ ∉ Vt M (LB M Q B) B Z t) ∧
  (∀ x, ConjMod M Q t x → ⁅x, t⁆ ∈ Q → ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅x, v⁆ ∈ Z)

@[expose] def Conc71abcd (hc : Ctx M Q Z B) (n : ℕ) (t : G) : Prop :=
  Conc71a hc t ∨ Conc71b hc n t ∨ Conc71c hc n t ∨ Conc71d hc n t

end CFSG.RankThree.GF2n.Stroth80
