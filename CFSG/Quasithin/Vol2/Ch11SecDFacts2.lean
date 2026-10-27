module

public import CFSG.Quasithin.Vol2.Ch11SecDFacts

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

@[expose] def TwoPointsFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ : Subgroup G),
    NatSetting11 G T L I n → (KindSL3 L (fsuV T I) n ∨ KindSp4 L (fsuV T I) n) →
    IsVi T L I n 1 V₁ → ∀ y₁ ∈ L, ∀ y₂ ∈ L, conjSubgroup V₁ y₁ ≠ conjSubgroup V₁ y₂ →
      conjSubgroup (LOf L V₁) y₁ ⊔ conjSubgroup (LOf L V₁) y₂ = L

@[expose] def CardVFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ),
    NatSetting11 G T L I n →
      (KindSL3 L (fsuV T I) n → Nat.card (fsuV T I) = 2 ^ (3 * n)) ∧
      (KindSp4 L (fsuV T I) n → Nat.card (fsuV T I) = 2 ^ (4 * n))

@[expose] def RankV2Fact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₂ : Subgroup G),
    NatSetting11 G T L I n → (KindSL3 L (fsuV T I) n ∨ KindSp4 L (fsuV T I) n) →
    IsVi T L I n 2 V₂ → ∀ A : Subgroup G, A ≤ T → IsElemAbelian 2 A →
      E3.mQuot A (A ⊓ Subgroup.centralizer (V₂ : Set G)) ≤ n

@[expose] def PointCommFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G),
    NatSetting11 G T L I n → (KindSL3 L (fsuV T I) n ∨ KindSp4 L (fsuV T I) n) →
    IsVi T L I n 1 V₁ → IsVi T L I n 2 V₂ → ∀ a ∈ T, ∀ y ∈ L,
      ⁅V₂, Subgroup.zpowers a⁆ ≤ conjSubgroup V₁ y →
        ⁅V₂, Subgroup.zpowers a⁆ = ⊥ ∨ ⁅V₂, Subgroup.zpowers a⁆ = V₁

end CFSG.Quasithin.Vol2.Ch11.SecD
