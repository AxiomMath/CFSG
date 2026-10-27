module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.Context
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
public import CFSG.LocalAnalysis.UniquenessCase.UC22InS3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

@[expose] def CommV2329 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx23L D Ch, 3 ≤ CFSG.Open.pRank 2 D.Z →
    ∀ T₀ : Subgroup G, T₀ ≤ D.T → D.T ≤ Subgroup.normalizer (T₀ : Set G) →
      (∃ g ∈ D.T, D.T ≤ T₀ ⊔ Subgroup.zpowers g) →
      ∀ U : Subgroup G, U ≤ T₀ → ⁅T₀, U⁆ ≤ D.Z → ⁅c.V, U⁆ = ⊥

@[expose] def OffenderV2329 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx23L D Ch,
    InS3.omegaOneZJ (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T)) ≤ InS3.thompsonJ D.T ∧
    c.V ≤ InS3.thompsonJ D.T ∧
    (c.L ≤ InS3.thompsonJ (c.L ⊔ D.T) →
      ⁅c.L, CFSG.RankThree.PartOne.omegaOneCenterIn (CFSG.Open.pCoreOf 2 (c.L ⊔ D.T))⁆ = c.V)

@[expose] def Push2329 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx23L D Ch, 3 ≤ CFSG.Open.pRank 2 D.Z →
    ∀ T₀ : Subgroup G, T₀ ≤ D.T → D.T ≤ Subgroup.normalizer (T₀ : Set G) →
      (∃ g ∈ D.T, D.T ≤ T₀ ⊔ Subgroup.zpowers g) → c.V ≤ T₀ → InS3.thompsonJ D.T ≤ T₀ →
      ∀ X : Subgroup G, X ≤ Subgroup.normalizer (T₀ : Set G) →
        X ≤ Subgroup.normalizer (D.Z : Set G) → X ≤ c.N

@[expose] def FieldGen2329 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx23L D Ch, 3 ≤ CFSG.Open.pRank 2 D.Z → ∀ K ∈ calC D.M,
    (K.subgroupOf D.M).Normal → ∀ e : ℕ, 2 ≤ e → IsL2 (Bar2 K) (2 ^ e) →
      ∀ t : G, ∀ ht : t ∈ Subgroup.normalizer (K : Set G), t ∈ D.T →
        ∃ x : Bar2 K, UC6S846.rhoL K ⟨t, ht⟩ ^ (2 ^ (e - 1)) = MulAut.conj x

end CFSG.LocalAnalysis.UniquenessCase.UC22
