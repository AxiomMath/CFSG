module

public import CFSG.RankThree.GF2n.Stroth80.Sec8Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Symplectic
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

@[expose] def Sec8CanonStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec8Hyp hc n t → ∀ r : G, Sec7A hc t r → ∀ g ∈ M,
      g ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) →
      g ∈ Subgroup.normalizer (Sec8V1 M Q Z B t r : Set G)

@[expose] def Sec8LemmaDStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec8Hyp hc n t → ∀ r : G, Sec7A hc t r → ∀ m : ℕ, SpMNat hc t m → ∀ g ∈ M,
      (∀ w ∈ Sec8W1 M Q Z B t r, ⁅g * t * g⁻¹, w⁆ ∈ Sec8V1 M Q Z B t r) →
      Z < Vt M (LB M Q B) B Z t ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t) ∧
      Nat.card Z ^ (m + 1) ≤
        Nat.card ↥(Sec8V1 M Q Z B t r ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t))

@[expose] def Sec8DPrimeStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec8Hyp hc n t → ¬ Conc81a hc t → ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ g ∈ M, Z < Vt M (LB M Q B) B Z t ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t) →
      ∃ h ∈ Rt M (LB M Q B) t, conjSubgroup g Z0 ≤ conjSubgroup h (LB M Q B) ⊓ hc.CN t

@[expose] def Sec8InvolStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec8Hyp hc n t → ∀ r : G, Sec7A hc t r → ∀ x ∈ H0 M Z, x ^ 2 ∈ Q →
      x ∈ Subgroup.normalizer (Sec8V1 M Q Z B t r : Set G) →
      (∀ v ∈ Vt M (LB M Q B) B Z t, ⁅x, v⁆ ∈ Z) →
      ∀ v ∈ Sec8V1 M Q Z B t r, ⁅x, v⁆ ∈ Vt M (LB M Q B) B Z t

@[expose] def Sec8TypeCountStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec8Hyp hc n t → ∀ r : G, Sec7A hc t r → ¬ Conc81a hc t → ∀ g ∈ M, ⁅g * t * g⁻¹, t⁆ ∈ Q →
      g * t * g⁻¹ ∈ Subgroup.normalizer (Sec8V1 M Q Z B t r : Set G) →
      (∀ v ∈ Sec8V1 M Q Z B t r, ⁅g * t * g⁻¹, v⁆ ∈ Z) →
      (∃ w ∈ Sec8W1 M Q Z B t r, ⁅g * t * g⁻¹, w⁆ ∉ Sec8V1 M Q Z B t r) → SpMNat hc t 2

@[expose] def Sec8PointTIStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Ctx M Q Z B → ∀ g ∈ M,
    (∃ d ∈ (B ⊔ Z : Subgroup G), d ∈ (conjSubgroup g B ⊔ Z : Subgroup G) ∧ d ∉ Z) →
      conjSubgroup g B ⊔ Z = B ⊔ Z

@[expose] def Sec8PointsTransStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec8Hyp hc n t → ∀ v ∈ Vt M (LB M Q B) B Z t, v ∉ Z →
      ∃ h ∈ Rt M (LB M Q B) t, v ∈ conjSubgroup h B ⊔ Z

@[expose] def Sec8LemmaHStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec8Hyp hc n t → ∀ r : G, Sec7A hc t r → ∀ m : ℕ, SpMNat hc t m → ∀ g ∈ M,
      g ∈ Subgroup.normalizer (LB M Q B : Set G) →
      (∀ v ∈ Vt M (LB M Q B) B Z t, g * v * g⁻¹ ∈ Sec8W1 M Q Z B t r) →
      Nat.card Z ^ (m + 1) ≤
        Nat.card ↥(Sec8V1 M Q Z B t r ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t)) →
      g ∈ Subgroup.normalizer (Rt M (LB M Q B) t : Set G)

@[expose] def Sec8CommNStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec8Hyp hc n t → ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
      ⁅hc.CN t, hc.CN t⁆ ≤ Z0

@[expose] def Close82FalseStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t r : G),
    Close82Hyp hc n t r → False

end CFSG.RankThree.GF2n.Stroth80
