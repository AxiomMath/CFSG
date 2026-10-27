module

public import CFSG.RankThree.PartOne.S11d.Facts5

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.Assembly.RankThreeEven (localRank)

@[expose] def ThreeComponentsCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (J₁ J₂ : Subgroup G) (u₁ u₂ : G),
    FieldAutSetting p J₁ u₁ → FieldAutSetting p J₂ u₂ → FieldAutRank p J₁ u₁ →
    FieldAutRank p J₂ u₂ → u₁ ^ p = 1 → u₂ ^ p = 1 → 2 ≤ CFSG.pRank p ↥J₁ →
    localRank p ↥(J₁ ⊔ Subgroup.zpowers u₁) ≤ 2 → localRank p ↥(J₂ ⊔ Subgroup.zpowers u₂) ≤ 2 →
    inSubgroup perfectResidual (J₁ ⊓ Subgroup.centralizer ({u₁} : Set G)) =
      inSubgroup perfectResidual (J₂ ⊓ Subgroup.centralizer ({u₂} : Set G)) →
    ∀ d : G, d ∈ J₁ → d ∈ J₂ → d ≠ 1 → d ^ p = 1 → u₁ * d = d * u₁ → u₂ * d = d * u₂ →
      (∃ S : Subgroup G, S ≤ J₁ ∧ S ≠ ⊥ ∧ IsPGroup 2 S ∧
        u₁ ∈ Subgroup.normalizer (S : Set G) ∧ d ∈ Subgroup.normalizer (S : Set G)) →
      (∃ S : Subgroup G, S ≤ J₂ ∧ S ≠ ⊥ ∧ IsPGroup 2 S ∧
        u₂ ∈ Subgroup.normalizer (S : Set G) ∧ d ∈ Subgroup.normalizer (S : Set G)) →
      ∃ K₁ K₂ : Subgroup G, IsComponentOf (J₁ ⊓ Subgroup.centralizer ({d} : Set G)) K₁ ∧
        IsComponentOf (J₂ ⊓ Subgroup.centralizer ({d} : Set G)) K₂ ∧
        u₁ ∈ Subgroup.normalizer (K₁ : Set G) ∧ u₂ ∈ Subgroup.normalizer (K₂ : Set G) ∧
        ∃ x ∈ K₂, ∃ hx : x ∈ K₁, (⟨x, hx⟩ : ↥K₁) ∉ Subgroup.center ↥K₁


@[expose] def ThreeComponents : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (J₁ J₂ : Subgroup G) (u₁ u₂ : G),
    FieldAutSetting p J₁ u₁ → FieldAutSetting p J₂ u₂ → FieldAutRank p J₁ u₁ →
    FieldAutRank p J₂ u₂ → u₁ ^ p = 1 → u₂ ^ p = 1 → 2 ≤ CFSG.pRank p ↥J₁ →
    localRank p ↥(J₁ ⊔ Subgroup.zpowers u₁) ≤ 2 → localRank p ↥(J₂ ⊔ Subgroup.zpowers u₂) ≤ 2 →
    inSubgroup perfectResidual (J₁ ⊓ Subgroup.centralizer ({u₁} : Set G)) =
      inSubgroup perfectResidual (J₂ ⊓ Subgroup.centralizer ({u₂} : Set G)) →
    ∀ d : G, d ∈ J₁ → d ∈ J₂ → d ≠ 1 → d ^ p = 1 → u₁ * d = d * u₁ → u₂ * d = d * u₂ →
      (∃ S : Subgroup G, S ≤ J₁ ∧ S ≠ ⊥ ∧ IsPGroup 2 S ∧
        u₁ ∈ Subgroup.normalizer (S : Set G) ∧ d ∈ Subgroup.normalizer (S : Set G)) →
      (∃ S : Subgroup G, S ≤ J₂ ∧ S ≠ ⊥ ∧ IsPGroup 2 S ∧
        u₂ ∈ Subgroup.normalizer (S : Set G) ∧ d ∈ Subgroup.normalizer (S : Set G)) →
      ∃ K₁ K₂ : Subgroup G, IsComponentOf (J₁ ⊓ Subgroup.centralizer ({d} : Set G)) K₁ ∧
        IsComponentOf (J₂ ⊓ Subgroup.centralizer ({d} : Set G)) K₂ ∧
        u₁ ∈ Subgroup.normalizer (K₁ : Set G) ∧ u₂ ∈ Subgroup.normalizer (K₂ : Set G) ∧
        FieldLike p u₁ K₁ ∧ FieldLike p u₂ K₂ ∧
        ∃ x ∈ K₂, ∃ hx : x ∈ K₁, (⟨x, hx⟩ : ↥K₁) ∉ Subgroup.center ↥K₁

end CFSG.RankThree.PartOne
