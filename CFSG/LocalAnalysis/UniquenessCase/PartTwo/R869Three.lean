module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xKGammaLemmas
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69S7
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R856Three
import CFSG.LocalAnalysis.UniquenessCase.UC7R71Three
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72.RankThree
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.PartOneSixThirtyEight
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.PartOneSixNine
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight70CoreInst
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69S7J4Rank
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69Main
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69S7L34
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CatalogModels
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Main
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK329InLie
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK329InHeavy
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK329InExcY
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK329InExcO3
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69R870Ne3
import CFSG.LocalAnalysis.UniquenessCase.UC22R847ThinNe3Setup
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229SEFZHolds
import CFSG.LocalAnalysis.UniquenessCase.UC22P22th
import CFSG.RankThree.PartTwo.Sec11.Item116R2K1
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69R872
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK335HMain
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK335HZStar
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK335HNormM24
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK335HNormHe
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK335HNormRu
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK335HNormJ4
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69S7MMax
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneL62Holds
public import CFSG.LocalAnalysis.UniquenessCase.OpenThree.R82Exits
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69R873
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.Case812Setup
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.R82Setup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three

open CFSG.LocalAnalysis.RankThreeUC (Setup Standing AGL81TheoremC)

variable {G : Type} [Group G] [Finite G]



theorem r869_dataOfSetup_of_inputs
    (hGF : CFSG.Yardstones.Me2c15c2c995a.GF2nCatalogClause)
    (hS : Standing G) (hUC : CFSG.Open.rankThreeUC G) (hC : AGL81TheoremC G) (S : Setup G)
    (hMS : S.InMSigma) : UC22.F08.R869 (dataOfSetup hS S) := by
  have hK335 : PartOne.Section8.K335 := PartOne.Section8.k335_of_oddZStar
    PartOne.Section8.k335OddZStar_holds PartOne.Section8.k335SporNormAt_M24
    PartOne.Section8.k335SporNormAt_He PartOne.Section8.k335SporNormAt_Ru
    PartOne.Section8.k335SporNormAt_J4
  have hCent : PartOne.Section8.McLThreeCentralizerOrders :=
    CFSG.RankThree.PartTwo.KFacts.K426Rest.mclThreeCentralizerCard
  have hMax : PartOne.Section8.McLThreeFiveMax := PartOne.Section8.mclThreeFiveMax_holds
  have hSE5 := PartOne.Section7.SEFive.stronglyEmbeddedFive_holds
  have hG3 := CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.gls3StronglyThreeEmbeddedPlus_holds
  have hSE3 : PartOne.Section7.StronglyEmbeddedThree :=
    PartOne.Section7.StronglyEmbeddedThree_of_KIB hG3 CFSG.AGLEmbedding.kFactCatalogSchreier_holds
      (PartOne.Section7.StronglyEmbeddedThreeKIB_of_small hG3 PartOne.Section7.KIB3Small_holds)
  have hK36 := UCK.k36_of_eqlStar
      (UCK.k36EqlStar_of_catalog CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds
          UCK.k36OddDefChar_holds UCK.k315Spor_holds UCK.k36EqlStarSporGe4_holds) UCK.l34OuterFree
  have hK328 : PartOne.Section8.K328 := PartOne.Section8.K328.k328_holds
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  have hSg := UC6S846.sigmaStd_dataOfSetup hS S
  have h63 := r6_3_dataOfSetup hS hUC hC S
  have h614 : UC6.R6_14 (dataOfSetup hS S) := UC6G.uc_theorem_6_14_three hS hUC hC hK36 S
  have hSQ : PartOne.Section7.StronglyEmbeddedSolvableQ :=
    PartOne.Section7.stronglyEmbeddedSolvableQ_of_kFacts UCK.kFactSmallIdent_holds
      UCK.kFactOneLieTorus_holds UCK.stronglyEmbeddedCyclicOuter_holds
      CFSG.AGLEmbedding.kFactCatalogSchreier_holds
      CFSG.AGLEmbeddingD2.Wilson.Coordinator.d2HeisLocalAt_J4
  have h847 : UC22.R847ThinNe3 (dataOfSetup hS S) :=
    UC22.r847ThinNe3_dataOfSetup hSE5 PartOne.Section7.stronglyEmbeddedFiveZ_holds
      PartTwo.thinList13_holds CFSG.RankThree.PartTwo.Sec11.cyclicSylowThreeOutAbelian_holds hSQ
      hSE3 hG3 CFSG.AGLEmbedding.kFactReeInvolution hS S
  have h870 : PartOne.Section8.R870 (dataOfSetup hS S) :=
    PartOne.Section8.r870_of_r847ThinNe3 _ hSE3
      (PartOne.Section7.stronglyEmbeddedSolvableAltTen_of_kFacts
          CFSG.LocalAnalysis.UniquenessCase.UCK.kFactSmallIdent_holds
          CFSG.LocalAnalysis.UniquenessCase.UCK.kFactOneLieTorus_holds
          CFSG.LocalAnalysis.UniquenessCase.UCK.stronglyEmbeddedCyclicOuter_holds
          CFSG.AGLEmbedding.kFactCatalogSchreier_holds
          CFSG.AGLEmbeddingD2.Wilson.Coordinator.d2HeisLocalAt_J4) hSg
      (PartOne.Section8.sec7CoreOdd_dataOfSetup hSE5 hS hUC hC S) h847
  have h872 : PartOne.Section8.R872 (dataOfSetup hS S) :=
    PartOne.Section8.r872_of_inputs _
      CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.kFactSuzukiThreeFree_holds hSg h614
      (r76Sig_dataOfSetup hSE5 hSE3 hS S) h870
  have hY : PartOne.Section8.Eight73YLieModel (dataOfSetup hS S) :=
    PartOne.Section8.eight73YLieModel_of_inputs
      CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement UCK.k35w_holds
      PartOne.Section8.stronglyEmbeddedCentralFree_holds h63
  have hS7 : PartOne.Section8.S7_876 (dataOfSetup hS S) :=
    PartOne.Section8.s7_876_of_inputs _ (r71_dataOfSetup hS S h63)
      (PartOne.Section7.R72.r72_dataOfSetup hS hUC hC S) CFSG.Sporadic.McL.isSimpleGroup_McL
      CFSG.Sporadic.McL.card_McL CFSG.RankThree.PartTwo.Sec4.card_outer_McL
      CFSG.Sporadic.Recognition.McLMultiplier.card_center_dvd_three_of_certificate hCent hMax
      (PartOne.Section8.s7ListL34_of UCK.kTits_holds PartTwo.S19.k_titsOddPrimes_holds) PartOne.Section8.s7J4Rank_holds
  have h82 : UC22.F08.R82 (dataOfSetup hS S) :=
    PartOne.Theorem82E3.r82_dataOfSetup_of_exits hGF
      PartOne.Theorem82E3.onanExcludedSetup_of_finiteFacts
      PartOne.Theorem82E3.l62ExcludedSetup_of_certificates
      (PartOne.Theorem82E3.case812Setup_of_scExcluded PartOne.Theorem82E3.scExcludedSetup_holds)
      hS hUC hC S hMS
  exact PartOne.Section8.r869_of_inputs _ h63 (r6_9_dataOfSetup hS hUC hC hK36 S) h614
    (r6_38_dataOfSetup hS S) (r76_dataOfSetup hSE5 hSE3 hS hUC hC S) hSg h870
    h82 (PartOne.Section8.r856_dataOfSetup hS hUC hC S hMS) h872
    (r6_7_dataOfSetup hS hUC hC hK36 S) hK328 (PartOne.Section8.k329_of_inputs
        PartOne.Section8.k329LieTypeStatement_holds PartOne.Section8.k329HeavyRankStatement_holds
        PartOne.Section8.k329ExceptionalYStatement_holds
        PartOne.Section8.k329ExceptionalO3Statement_holds) hK335 hY hS7

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three
