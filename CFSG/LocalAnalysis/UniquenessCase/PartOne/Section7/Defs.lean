module

public import CFSG.Open.RankThreeDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def Conclusion76 (M : Subgroup G) (p : ℕ) : Prop :=
  ∀ r : ℕ, r.Prime → ∀ E : Subgroup G, E ≤ M → CFSG.Open.IsElemAbelian r E →
    Nat.card E = r ^ 2 → 0 < CFSG.Open.pRank p (M ⊓ centralizer (E : Set G)) →
    (∀ X : Subgroup G, X ≤ E → Nat.card X = r →
      1 < CFSG.Open.pRank p (M ⊓ normalizer (X : Set G))) →
    CFSG.Open.rankThreeGamma 1 r E ≤ M

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
