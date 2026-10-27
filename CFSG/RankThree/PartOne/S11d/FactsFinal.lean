module

public import CFSG.RankThree.PartOne.S11d.Facts11

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG

@[expose] def OutPCyclic : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (J : Subgroup G) (a : G), FieldAutSetting p J a →
    CFSG.pRank p ↥J ≤ 1 →
    ∀ u v : G, u ∈ normalizer (J : Set G) → v ∈ normalizer (J : Set G) → u * v = v * u →
      (∃ k : ℕ, orderOf u = p ^ k) → (∃ k : ℕ, orderOf v = p ^ k) →
      u ∈ zpowers v ⊔ (J ⊔ centralizer (J : Set G)) ∨
        v ∈ zpowers u ⊔ (J ⊔ centralizer (J : Set G))

end CFSG.RankThree.PartOne
