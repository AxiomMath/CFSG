module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R8107OutSetup
public import CFSG.LocalAnalysis.UniquenessCase.UC22R847O3
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.Three
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36SporGe4
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36ODCCent
public import CFSG.LocalAnalysis.UniquenessCase.UC6K316Out
public import CFSG.LieType.SeitzGeneration.SeitzStatus
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36SporPairs
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229SEFZHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.Holds
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229KThin
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3ThreeKIBA6
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Conclusion76Three

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three

open CFSG.LocalAnalysis.UniquenessCase.UC22


variable {G : Type} [Group G] [Finite G]

theorem r8107_three
    (hS : RankThreeUC.Standing G) (hUC : CFSG.Open.rankThreeUC G)
    (hC : RankThreeUC.AGL81TheoremC G) (S : RankThreeUC.Setup G)
    (h82 : F08.R82 (dataOfSetup hS S)) : F08.R8107 (dataOfSetup hS S) := by
  have hSE5 := PartOne.Section7.SEFive.stronglyEmbeddedFive_holds
  have hSE3 := PartOne.Section7.StronglyEmbeddedThree_of_KIB
    RankThreeTheoremC.KFactProofs.gls3StronglyThreeEmbeddedPlus_holds
    CFSG.AGLEmbedding.kFactCatalogSchreier_holds
    (PartOne.Section7.StronglyEmbeddedThreeKIB_of_small
      RankThreeTheoremC.KFactProofs.gls3StronglyThreeEmbeddedPlus_holds
      PartOne.Section7.KIB3Small_holds)
  have hSg := UC6S846.sigmaStd_dataOfSetup hS S
  exact R8107Out.r8107_dataOfSetup hSE5 KBridge.kThinSimple_holds hS S hSg h82
    (R847O3.r847OrderThree_dataOfSetup hSE5 PartOne.Section7.stronglyEmbeddedFiveZ_holds
      KBridge.kThinSimple_holds hS S hSg)
    (r76Sig_dataOfSetup hSE5 hSE3 hS S)
    (UC6G.uc_theorem_6_14_three hS hUC hC (UCK.k36_of_eqlStar
        (UCK.k36EqlStar_of_catalog CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds
            UCK.k36OddDefChar_holds UCK.k315Spor_holds UCK.k36EqlStarSporGe4_holds) UCK.l34OuterFree) S)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three
