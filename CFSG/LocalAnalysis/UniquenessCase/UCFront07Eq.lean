module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F07

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

@[expose] def R77Eq (D : Data G) : Prop :=
  D.sig ⊆ D.sig1 → ∀ p ∈ D.sig, p ≠ 2 → IsStronglyPEmbedded p D.M →
    ∀ r : ℕ, r.Prime → r ≠ 2 → r ∉ D.sig →
      ∀ X : Subgroup G, X ≤ D.M → IsPGroup r X → ¬ IsCyclic X → (∀ x ∈ X, x ^ r = 1) →
        ⁅⁅X, X⁆, X⁆ = ⊥ → 2 < CFSG.Open.pRank p (D.M ⊓ normalizer (X : Set G)) →
        CFSG.Open.pRank p D.M = CFSG.Open.pRank p (D.M ⊓ normalizer (X : Set G)) →
          rankThreeGamma 1 r X ≤ D.M

end CFSG.LocalAnalysis.UniquenessCase.UC22.F07
