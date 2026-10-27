module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F08

open CFSG.Open
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

@[expose] def R880J4 (D : Data G) : Prop :=
  ∀ L ∈ calC D.M, IsSpor (Bar2 L) .J4 → ¬ IsStronglyPEmbedded 3 D.M → D.sig = {11} → False

end CFSG.LocalAnalysis.UniquenessCase.UC22.F08
