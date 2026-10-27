module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72.RankThree
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R856Three
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3ThreeKIBA6

public section
namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
open CFSG.LocalAnalysis.RankThreeUC (Setup Standing AGL81TheoremC)

theorem r891_dataOfSetup_of_d4Core

    {G : Type} [Group G] [Finite G]
    (hS : Standing G) (hUC : CFSG.Open.rankThreeUC G) (hC : AGL81TheoremC G) (S : Setup G)
    (hMS : S.InMSigma) :
    UC22.F08.R891 (PartTwo.Three.dataOfSetup hS S) := by
  have hSE5 := Section7.SEFive.stronglyEmbeddedFive_holds
  have hG3 := CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.gls3StronglyThreeEmbeddedPlus_holds
  have hSE3 : Section7.StronglyEmbeddedThree :=
    Section7.StronglyEmbeddedThree_of_KIB hG3 CFSG.AGLEmbedding.kFactCatalogSchreier_holds
      (Section7.StronglyEmbeddedThreeKIB_of_small hG3 Section7.KIB3Small_holds)
  exact r891_of_inputs (PartTwo.Three.dataOfSetup hS S) (UC6S846.sigmaStd_dataOfSetup hS S)
    (PartTwo.Three.r6_3_dataOfSetup hS hUC hC S) (Section7.R72.r72_dataOfSetup hS hUC hC S)
    (PartTwo.Three.r76Sig_dataOfSetup hSE5 hSE3 hS S) (r856_dataOfSetup hS hUC hC S hMS)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
