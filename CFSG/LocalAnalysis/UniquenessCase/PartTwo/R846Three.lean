module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S846k
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.Three
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Conclusion76Three

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (StronglyEmbeddedFive StronglyEmbeddedThree)


variable {G : Type} [Group G] [Finite G]

theorem r846_dataOfSetup
    (hgr : CFSG.Open.GriessAllModelsStatement) (hSE : StronglyEmbeddedFive)
    (hSE3 : StronglyEmbeddedThree) (hS : Standing G) (hUC : rankThreeUC G)
    (hC : AGL81TheoremC G) (hK : UCK.K36) (S : Setup G) : UC22.F08.R846 (dataOfSetup hS S) :=
  UC6S846.r846_of_rank_three hgr _ (UC6S846.sigmaStd_dataOfSetup hS S)
    (r76Sig_dataOfSetup hSE hSE3 hS S) (UC6G.uc_theorem_6_14_three hS hUC hC hK S)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three
