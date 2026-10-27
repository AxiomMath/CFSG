module

public import CFSG.RankThree.PartOne.S12.InputsEleven

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.Blueprint (EvenLieType)

@[expose] def FieldAutSetting {G : Type} [Group G] [Finite G] (p : ℕ) (J : Subgroup G) (u : G) :
    Prop :=
  p.Prime ∧ 5 ≤ p ∧ CFSG.IsQuasisimple ↥J ∧ EvenLieType (↥J ⧸ Subgroup.center ↥J) ∧
    evenRank ↥(J ⊔ Subgroup.zpowers u) ≤ 3 ∧ ¬ p ∣ Nat.card (Subgroup.center ↥J) ∧
    InducesFieldAut p u J

@[expose] def FieldAutRank {G : Type} [Group G] [Finite G] (p : ℕ) (J : Subgroup G) (u : G) :
    Prop :=
  evenRank G ≤ 3 ∧ ∃ c ∈ Subgroup.centralizer (J : Set G), c ≠ 1 ∧ c ^ p = 1 ∧ u * c = c * u

@[expose] def FieldFixedPElements : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (J : Subgroup G) (u : G), FieldAutSetting p J u →
    u ^ p = 1 → FieldAutRank p J u →
    ∀ g ∈ J ⊓ Subgroup.centralizer ({u} : Set G), (∃ k : ℕ, orderOf g = p ^ k) →
      g ∈ inSubgroup perfectResidual (J ⊓ Subgroup.centralizer ({u} : Set G))

@[expose] def FieldFixedCentralizer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (J : Subgroup G) (u : G), FieldAutSetting p J u →
    u ^ p = 1 → FieldAutRank p J u →
    ∀ g : ↥J, (∀ e ∈ inSubgroup perfectResidual (J ⊓ Subgroup.centralizer ({u} : Set G)),
      (g : G) * e = e * (g : G)) → g ∈ Subgroup.center ↥J

@[expose] def FieldFixedNonLocal : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (J : Subgroup G) (u : G), FieldAutSetting p J u →
    u ^ p = 1 → FieldAutRank p J u →
    ∀ S : Subgroup G, S ≤ J → IsPGroup 2 S →
      inSubgroup perfectResidual (J ⊓ Subgroup.centralizer ({u} : Set G)) ≤
        Subgroup.normalizer (S : Set G) →
      ⁅S, inSubgroup perfectResidual (J ⊓ Subgroup.centralizer ({u} : Set G))⁆ = ⊥

end CFSG.RankThree.PartOne
