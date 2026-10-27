module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34L3PSig
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataThree
public import CFSG.LocalAnalysis.UniquenessCase.UCK35wHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KIZHolds
public import CFSG.HardMathSupport.Foote.FamilyReduction.ClassicalFive
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.Holds
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3ThreeKIBA6
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Conclusion76Three
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.PartOneThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.LocalAnalysis.RankThreeUC (Setup Standing AGL81TheoremC)

variable {G : Type} [Group G] [Finite G]

theorem r149L3P_dataOfSetup
    (hS : Standing G) (hUC : CFSG.Open.rankThreeUC G) (hC : AGL81TheoremC G) (S : Setup G) :
    R149L3P (PartTwo.Three.dataOfSetup hS S) := by
  have hG3 := RankThreeTheoremC.KFactProofs.gls3StronglyThreeEmbeddedPlus_holds
  have hSE3 := PartOne.Section7.StronglyEmbeddedThree_of_KIB hG3
    CFSG.AGLEmbedding.kFactCatalogSchreier_holds
    (PartOne.Section7.StronglyEmbeddedThreeKIB_of_small hG3 PartOne.Section7.KIB3Small_holds)
  exact uc22s2112l3p_r149_of_sigmaStd
    CFSG.HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement UCK.k35w_holds
    PartOne.Section8.stronglyEmbeddedCentralFree_holds (UC6S846.sigmaStd_dataOfSetup hS S)
    (PartTwo.Three.r76Sig_dataOfSetup PartOne.Section7.SEFive.stronglyEmbeddedFive_holds hSE3 hS S)
    (PartTwo.Three.r6_3_dataOfSetup hS hUC hC S)

end CFSG.LocalAnalysis.UniquenessCase.UC22
