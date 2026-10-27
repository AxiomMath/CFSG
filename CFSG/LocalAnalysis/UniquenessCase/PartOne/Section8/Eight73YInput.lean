module

public import CFSG.RankThree.PartOne.S12.InputsSec15

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

@[expose] def StronglyEmbeddedCentralFree : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 →
    ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → CFSG.pPrimeCore p X = ⊥ →
      2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) → ∀ N : Subgroup X, IsStronglyPEmbedded p N →
        ∀ P : Sylow p X, ∀ x ∈ (P : Subgroup X),
          (∀ n ∈ Subgroup.normalizer ((P : Subgroup X) : Set X), x * n = n * x) → x = 1

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
