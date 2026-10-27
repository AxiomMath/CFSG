module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3Defs
import CFSG.CGT.PushingUpLit.Transport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76 StronglyEmbeddedThree)

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_17RV (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx21 D Ch, ∀ L ∈ calC D.M, ¬ (L.subgroupOf D.M).Normal →
    IsJ1 (Bar2 L) → CFSG.Open.evenRank G = 3

end CFSG.LocalAnalysis.UniquenessCase.UC22
