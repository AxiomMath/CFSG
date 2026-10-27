module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F08

open CFSG.Open
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

@[expose] def R880J4G {G : Type} [Group G] [Finite G] (D : Data G) : Prop :=
  ∀ L ∈ calC D.M, IsSpor (Bar2 L) .J4 → ¬ IsStronglyPEmbedded 3 D.M → D.sig = {11} →
    ∀ Q : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 Q L → rankThreeGamma 1 3 Q ≤ D.M → False

end CFSG.LocalAnalysis.UniquenessCase.UC22.F08
