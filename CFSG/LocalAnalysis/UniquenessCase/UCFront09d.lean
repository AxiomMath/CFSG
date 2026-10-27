module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def R923K1 (D : Data G) : Prop :=
  D.k = 1 →
  ∀ L ∈ calC D.M, L ≤ D.M → D.M ≤ normalizer (L : Set G) → IsAlt (Bar2 L) 5 →
    UniqueMax D.M (L ⊔ D.T) →
    ∀ X : Subgroup G, Opp 3 X = X → X ≤ L → L = X ⊔ pCoreOf 2 L →
      ⁅pCoreOf 2 D.M ⊓ centralizer (pCoreOf 2 D.M : Set G) ⊓ X, X⁆ ≠ ⊥ →
        calNOf X = {D.M}

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
