module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102R8103
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.Three
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36SporGe4
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36ODCCent
public import CFSG.LocalAnalysis.UniquenessCase.UC6K316Out
public import CFSG.LieType.SeitzGeneration.SeitzStatus
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36SporPairs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72.RankThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KStrongEmbedded72Holds
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3ThreeKIBA6

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.LocalAnalysis.RankThreeUC (Standing Setup AGL81TheoremC)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three (dataOfSetup)


theorem r8103_dataOfSetup_of_kFacts
    (hC : ∀ (G : Type) [Group G] [Finite G], Standing G → AGL81TheoremC G)
    (h82 : ∀ (G : Type) [Group G] [Finite G] (hS : Standing G), CFSG.Open.rankThreeUC G →
      ∀ S : Setup G, S.InMSigma → UC22.F08.R82 (dataOfSetup hS S))
    (hK1 : KU4OddRank) (hK2 : KU45Syl3) (hK3 : KU45Key) (hK4 : KU4SylOdd) (hK5 : KU45Types)
    (hK6 : KU45Out) (hK7 : KU45TorusFix) (hK8 : KAltTen) (hK9 : KU45AltFive) :
    ∀ (G : Type) [Group G] [Finite G] (hS : Standing G), CFSG.Open.rankThreeUC G →
      ∀ S : Setup G, S.InMSigma →
        CFSG.LocalAnalysis.UniquenessCase.UC22.F08.R8103 (dataOfSetup hS S) :=
  fun G _ _ hS hUC S hMS =>
    r8103_of_inputs (dataOfSetup hS S) (UC6S846.sigmaStd_dataOfSetup hS S) hS.rank
      (h82 G hS hUC S hMS)
      (UC6G.uc_theorem_6_14_three hS hUC (hC G hS) (UCK.k36_of_eqlStar
          (UCK.k36EqlStar_of_catalog CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds
              UCK.k36OddDefChar_holds UCK.k315Spor_holds UCK.k36EqlStarSporGe4_holds)
          UCK.l34OuterFree) S)
      (PartTwo.Three.r76Sig_dataOfSetup Section7.SEFive.stronglyEmbeddedFive_holds
        (Section7.StronglyEmbeddedThree_of_KIB
          RankThreeTheoremC.KFactProofs.gls3StronglyThreeEmbeddedPlus_holds
          CFSG.AGLEmbedding.kFactCatalogSchreier_holds
          (Section7.StronglyEmbeddedThreeKIB_of_small
            RankThreeTheoremC.KFactProofs.gls3StronglyThreeEmbeddedPlus_holds
            Section7.KIB3Small_holds)) hS S)
      (Section7.R72.r72_dataOfSetup hS hUC (hC G hS) S) UC22.kStrongEmbedded72_holds
      hK1 hK2 hK3 hK4 hK5 hK6 hK7 hK8 hK9

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
