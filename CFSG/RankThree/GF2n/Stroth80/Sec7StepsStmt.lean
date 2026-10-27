module

public import CFSG.RankThree.GF2n.Stroth80.Sec7Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

@[expose] def Sec7WVGeOm4Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → OmegaMinusNat hc t 2 → 8 ≤ n

@[expose] def Sec7CentreMprStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ x ∈ LB M Q B, (∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅x, w⁆ ∈ Z) → x ∈ Z0

@[expose] def Sec7CRWStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ y ∈ Rt M (LB M Q B) t, (∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅y, w⁆ ∈ Z) → y ∈ Z0

@[expose] def Sec7SchurStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ w ∈ H0 M Z, (∀ a ∈ ⁅Rt M (LB M Q B) t, Rt M (LB M Q B) t⁆, ⁅w, a⁆ ∈ Q) →
      (∀ u ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅w, u⁆ ∈ Z) → w ∈ Z0

@[expose] def Sec7SVStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ g ∈ M, (∀ v ∈ Vt M (LB M Q B) B Z t, ⁅g * t * g⁻¹, v⁆ ∈ Z) →
      ∀ y ∈ conjSubgroup g Z0, ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅y, v⁆ ∈ Z

@[expose] def Sec7SWStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ g ∈ M, (∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅g * t * g⁻¹, w⁆ ∈ Vt M (LB M Q B) B Z t) →
      ∀ y ∈ conjSubgroup g Z0, ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t),
        ⁅y, w⁆ ∈ Vt M (LB M Q B) B Z t

@[expose] def Sec7Q7Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ∀ g ∈ M, g ∈ Subgroup.normalizer (LB M Q B : Set G) →
    conjSubgroup g (Vt M (LB M Q B) B Z t) ≤ Wt Q (Vt M (LB M Q B) B Z t) →
    (∀ k ∈ hc.CN t,
      k ∈ Subgroup.normalizer (conjSubgroup g (Vt M (LB M Q B) B Z t) : Set G)) →
    conjSubgroup g (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t

@[expose] def Step71VanishBoundStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ Conc71abcd hc n t →
    (∃ x : G, ConjMod M Q t x ∧ ⁅x, t⁆ ∈ Q ∧ ∃ v ∈ Vt M (LB M Q B) B Z t, ⁅x, v⁆ ∉ Z) →
    ∀ m : ℕ, 2 ≤ m → (OmegaPlusNat hc t m ∨ OmegaMinusNat hc t m) → 2 * n ≤ 8 * m - 2

@[expose] def Step71VanishOmega10Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ Conc71abcd hc n t → OmegaPlusNat hc t 5 → n = 18 →
    ∀ x : G, ConjMod M Q t x → ⁅x, t⁆ ∈ Q → ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅x, v⁆ ∈ Z

@[expose] def Step71TypeSecStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ Conc71abcd hc n t →
    ∀ x : G, ConjMod M Q t x → ⁅x, t⁆ ∈ Q → (∀ v ∈ Vt M (LB M Q B) B Z t, ⁅x, v⁆ ∈ Z) →
    (∃ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅x, w⁆ ∉ Vt M (LB M Q B) B Z t) →
    ∃ P : Subgroup G, Vt M (LB M Q B) B Z t < P ∧ P ≤ Wt Q (Vt M (LB M Q B) B Z t) ∧
      (∀ r ∈ Rt M (LB M Q B) t, conjSubgroup r P = P) ∧
      (∀ k ∈ hc.CN t, ∀ y ∈ P, ⁅k, y⁆ ∈ Vt M (LB M Q B) B Z t) ∧
      (∃ r : G, Sec7A hc t r ∧ ∃ A₁ A₂ : Subgroup G,
        IsOppDecomp P (Vt M (LB M Q B) B Z t) (LB M Q B) (LB M Q (conjSubgroup r B)) A₁ A₂) ∧
      ∀ m : ℕ, 2 ≤ m → (OmegaPlusNat hc t m ∨ OmegaMinusNat hc t m) →
        Nat.card ↥P ≤ Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card Z ^ (2 * m)

@[expose] def Sec7WVSecOrderStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ∀ P : Subgroup G, Vt M (LB M Q B) B Z t < P →
    P ≤ Wt Q (Vt M (LB M Q B) B Z t) → (∀ r ∈ Rt M (LB M Q B) t, conjSubgroup r P = P) →
    (∀ k ∈ hc.CN t, ∀ y ∈ P, ⁅k, y⁆ ∈ Vt M (LB M Q B) B Z t) →
    (∃ r : G, Sec7A hc t r ∧ ∃ A₁ A₂ : Subgroup G,
      IsOppDecomp P (Vt M (LB M Q B) B Z t) (LB M Q B) (LB M Q (conjSubgroup r B)) A₁ A₂) →
    ∀ m : ℕ, 2 ≤ m →
    (OmegaMinusNat hc t m →
      Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card Z ^ (2 ^ m) ≤ Nat.card ↥P) ∧
    (OmegaPlusNat hc t m → 3 ≤ m →
      Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card Z ^ (2 ^ (m - 1)) ≤ Nat.card ↥P)

@[expose] def Sec73CardAlphaStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ Conc71abcd hc n t → OmegaMinusNat hc t 2 →
    ∀ α ∈ LB M Q B ⊓ hc.CN t, Nat.card ↥(Ut Q Z α) ≤ Nat.card Z ^ 8

@[expose] def Sec73CardBetaStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ Conc71abcd hc n t → OmegaMinusNat hc t 2 →
    ∀ β ∈ LB M Q B, β ∉ hc.CN t → Nat.card Z ^ (n + 1) ≤ Nat.card ↥(Ut Q Z β)

end CFSG.RankThree.GF2n.Stroth80
