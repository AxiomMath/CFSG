module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.UniquenessCase.UCFront13

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open
open CFSG.RankThree.PartOne (pElementSubgroup)

variable {G : Type} [Group G] [Finite G]

@[expose] def R136bFour (D : Data G) : Prop :=
  D.sig = D.sig1 → F13.Hyp131 D → ∀ p ∈ D.sig, ∀ B : Subgroup G, F13.Case136b D p B →
    CFSG.Open.pRank p D.M ≤ 3

end CFSG.LocalAnalysis.UniquenessCase.UC22
