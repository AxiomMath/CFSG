module

public import CFSG.RankThree.PartOne.S11d.Facts11

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.Assembly.LowTwoRank (StatedLieTag)
open CFSG.Blueprint (LieModel)

@[expose] def IsComponentOf {G : Type} [Group G] (X D : Subgroup G) : Prop :=
  D ≤ X ∧ CFSG.IsQuasisimple ↥D ∧ (D.subgroupOf X).IsSubnormal

@[expose] def InnerOnTheta {G : Type} [Group G] (p : ℕ) (I : Subgroup G) (u : G) : Prop :=
  ∃ hu : u ∈ Subgroup.normalizer (I : Set G), thetaQuotientConj p I ⟨u, hu⟩ ∈
    (MulAut.conj : (↥I ⧸ aschbacherSolvableCore p ↥I) →*
      MulAut (↥I ⧸ aschbacherSolvableCore p ↥I)).range

@[expose] def FieldLike {G : Type} [Group G] (p : ℕ) (u : G) (D : Subgroup G) : Prop :=
  u ∈ Subgroup.normalizer (D : Set G) ∧ u ∉ D ⊔ Subgroup.centralizer (D : Set G) ∧
    u ^ p ∈ D ⊔ Subgroup.centralizer (D : Set G) ∧
    ∃ (t : StatedLieTag) (n f : ℕ), 1 ≤ f ∧ LieModel (D ⧸ Subgroup.center D) t n 2 (p * f)

@[expose] def LieCentralizerComponent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (J : Subgroup G) (u : G), FieldAutSetting p J u →
    u ^ p = 1 → FieldAutRank p J u → CFSG.pRank p ↥J = 1 →
    ∀ d ∈ J, d ≠ 1 → d ^ p = 1 → u * d = d * u →
      (∃ t ∈ J ⊓ Subgroup.centralizer ({d} : Set G), orderOf t = 2) →
      ∃ D : Subgroup G, IsComponentOf (J ⊓ Subgroup.centralizer ({d} : Set G)) D

@[expose] def LieFieldOnComponent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (J : Subgroup G) (u : G), FieldAutSetting p J u →
    u ^ p = 1 → FieldAutRank p J u → ∀ d ∈ J, d ^ p = 1 → u * d = d * u →
      ∀ D : Subgroup G, IsComponentOf (J ⊓ Subgroup.centralizer ({d} : Set G)) D →
        u ∈ Subgroup.normalizer (D : Set G) →
        FieldLike p u D ∧ ∃ t₁ ∈ D ⊓ Subgroup.centralizer ({u} : Set G),
          ∃ t₂ ∈ D ⊓ Subgroup.centralizer ({u} : Set G), (∃ k : ℕ, orderOf t₁ = 2 ^ k) ∧
            (∃ k : ℕ, orderOf t₂ = 2 ^ k) ∧ t₁ * t₂ ≠ t₂ * t₁

@[expose] def FieldFixedTwoElements : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (J : Subgroup G) (u : G), FieldAutSetting p J u →
    u ^ p = 1 → FieldAutRank p J u →
    CFSG.pRank p ↥J = 1 → ∀ d ∈ J, d ≠ 1 → d ^ p = 1 → u * d = d * u →
      (∃ t ∈ J ⊓ Subgroup.centralizer ({d} : Set G), orderOf t = 2) →
      ∀ g ∈ J ⊓ Subgroup.centralizer ({u} : Set G),
        (∃ k : ℕ, orderOf g = 2 ^ k) →
        g ∈ inSubgroup perfectResidual (J ⊓ Subgroup.centralizer ({u} : Set G))

@[expose] def LieTwoPartInLayer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (J : Subgroup G) (u : G), FieldAutSetting p J u →
    u ^ p = 1 → FieldAutRank p J u → CFSG.pRank p ↥J = 1 → ∀ d ∈ J, d ^ p = 1 → u * d = d * u →
      ∀ g ∈ J ⊓ Subgroup.centralizer ({u} : Set G) ⊓ Subgroup.centralizer ({d} : Set G),
        (∃ k : ℕ, orderOf g = 2 ^ k) →
          g ∈ inSubgroup layer (J ⊓ Subgroup.centralizer ({d} : Set G))

@[expose] def LieGoodComponent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (J : Subgroup G) (u : G), FieldAutSetting p J u →
    u ^ p = 1 → FieldAutRank p J u → CFSG.pRank p ↥J = 1 →
    ∀ d ∈ J, d ≠ 1 → d ^ p = 1 → u * d = d * u →
      (∃ t ∈ J ⊓ Subgroup.centralizer ({d} : Set G), orderOf t = 2) →
      (∃ D : Subgroup G, IsComponentOf (J ⊓ Subgroup.centralizer ({d} : Set G)) D) ∧
      (∀ D : Subgroup G, IsComponentOf (J ⊓ Subgroup.centralizer ({d} : Set G)) D →
        FieldLike p u D ∧ ∃ t₁ ∈ D ⊓ Subgroup.centralizer ({u} : Set G),
          ∃ t₂ ∈ D ⊓ Subgroup.centralizer ({u} : Set G), (∃ k : ℕ, orderOf t₁ = 2 ^ k) ∧
            (∃ k : ℕ, orderOf t₂ = 2 ^ k) ∧ t₁ * t₂ ≠ t₂ * t₁) ∧
      ∀ g ∈ J ⊓ Subgroup.centralizer ({u} : Set G) ⊓ Subgroup.centralizer ({d} : Set G),
        (∃ k : ℕ, orderOf g = 2 ^ k) →
          g ∈ inSubgroup layer (J ⊓ Subgroup.centralizer ({d} : Set G))

@[expose] def FieldOnComponentOuter : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G),
    SteinbergBM.SectionTenSetup G p A → ∀ d ∈ A, d ≠ 1 → ∀ I ∈ thetaComponentsAt p d,
      ∀ u ∈ A, ∀ v ∈ A, ∀ E : Subgroup G,
        IsComponentOf (I ⊓ Subgroup.centralizer ({v} : Set G)) E →
        u ∈ Subgroup.normalizer (E : Set G) → FieldLike p u E → ¬ InnerOnTheta p I u

@[expose] def OutPCyclicTheta : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G),
    SteinbergBM.SectionTenSetup G p A → ∀ d ∈ A, d ≠ 1 → ∀ I ∈ thetaComponentsAt p d,
      ∀ u ∈ A, u ≠ 1 → ∀ v ∈ A, v ∉ Subgroup.zpowers u →
        ∃ b ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v, b ≠ 1 ∧ InnerOnTheta p I b

end CFSG.RankThree.PartOne
