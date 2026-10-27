module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Quasithin.H13.A7BlkAct
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.Open
open CFSG.Quasithin.H13.A7Blk (ptCore)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G]

theorem uc22s206s_not_stronglyEmbedded [Finite G] (D : Data G) (hk : D.k = 2) :
    ¬ IsStronglyPEmbedded 3 D.M := fun h => by
  have h1 : D.k = 1 := by
    show CFSG.LocalAnalysis.RankThreeUC.kParam D.M = 1
    rw [CFSG.LocalAnalysis.RankThreeUC.kParam, if_pos h]
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
