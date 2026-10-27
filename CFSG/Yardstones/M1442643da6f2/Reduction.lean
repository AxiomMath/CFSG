module

public import CFSG.Yardstones.M1442643da6f2.Definitions
public import CFSG.Milestones.CL_LIT_classical_involution_theorem
public import CFSG.LocalAnalysis.EvenSporadicStandard.Frontier.MilestoneNoA8
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.A6A6.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm54Reach.CTEvenSmallLieMilestone
import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.GH312.AlmostSimple
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveRhoMain
import CFSG.LocalAnalysis.SeitzReduction.SeitzFamiliesFinalElevenGLS3

public section

namespace CFSG.Yardstones.M1442643da6f2

open CFSG.EvenSporadicStandard CFSG.Blueprint.NativeSporadic CFSG.Milestones

theorem citPart2_of_models
    (h : type_of% @CFSG.Milestones.cl_lit_classical_involution_theorem_models) :
    Induction.CITPart2 :=
  fun G _ _ _ hF z hz J hzJ hJ S hS => (h G hF z hz J hzJ hJ S hS).2

section Certified


theorem ctss_models_of_yardstones
    (h01 : ConwayStandardInputs) (h02 : EgawaHarrisSolomonInputs)
    (h03 : CatalogueFixedComponentFacts) (h04 : Finkelstein76bOuterCase)
    (h05 : InvolutionCentralizerTheorems) (h06 : ONanInputs) (h07 : CatalogueCentralizerFacts)
    (h08 : AlternatingStandardFormInputs)
    (h09 : CFSG.ComponentClassification.GSThmB.Solomon2AnInput)
    (h10 : CharTwoLieStandardFormInputs) (h11 : HNRecognitionInputs)
    (h12 : ComponentTheoryLiterature) (h13 : Solomon78StandardFormLiterature)
    (h14 : FischerThompsonRowInputs) (h15 : TwoFi22RecognitionInputs)
    (h16 : OddStandardL34HeChildren)
    (hGH74 : type_of% @CFSG.Milestones.cl_lit_gh74_sectional_two_rank_four_models)
    (hCIT : type_of% @CFSG.Milestones.cl_lit_classical_involution_theorem_models)
    (hCTE : Induction.CTEvenResidualStatement) :
    ModelsStatement :=
  Frontier.ctss_models_of_frontier'
    (h01.fs79 h01.kdnp hCIT hGH74 hCTE (h16.l34 hCIT hGH74) (h16.he hCIT))
    h07.catZ2A6 HSStd.Zassenhaus.A6A6.prop21A6A6Case_proved h07.catZ2A7 h02.egawaHypA
    h02.harrisSolomon h07.catM10 h04.outerS16Loc h04.outerS84 h05.harada39One h05.harris311
    h05.harris311HiS h07.kgA6Sq h06.onan77S5 h06.onanNoSL29Y h07.catE16 h06.onanInspection
    h07.kgHS3
    (CFSG.ComponentClassification.RankTwoSporadic.HS.sporadicCaseOdd_HS
      CFSG.ComponentClassification.RankTwoFoundation.lemma32
      CFSG.ComponentClassification.RankTwoFoundation.lemma33Three)
    h03.kgPumpTableT h08.altStdFormBigStd (TwoHS.GH312.gh312Fixed_of_gh74 hGH74)
    (CFSG.SeitzReduction.seitzExclusion_highPSL_of_final11_gls3
      CFSG.SeitzReduction.LinearPilot.lFiveFieldTildeSplitInput_holds)
    h05.harada39Two
    (sol78LitCore_of_yardstones (citPart2_of_models hCIT) (h16.l34 hCIT hGH74) (h16.he hCIT) hCTE
      Induction.ctEvenSmallLieStatement_of_milestone h12 h13)
    h09
    h03.noFixedDoubleCover h11.haradaHN
    (Induction.Balance.StdUHered.of_catalog
      CFSG.ComponentClassification.FooteLit.catalogAlmostSimpleUnbalancedOutcome_holds)
    h05.ghLemma53_1
    (h10.thm54 (citPart2_of_models hCIT) hCTE)
    h14.hypOneFi24 h14.thSylowWreathPair h01.co2 h15.fi24Local hGH74
    h07.ds81Lemma210Two h14.fi22Covers h14.u62Covers
    (h14.u62OddExcl (citPart2_of_models hCIT))

theorem ctss_order_of_yardstones
    (h01 : ConwayStandardInputs) (h02 : EgawaHarrisSolomonInputs)
    (h03 : CatalogueFixedComponentFacts) (h04 : Finkelstein76bOuterCase)
    (h05 : InvolutionCentralizerTheorems) (h06 : ONanInputs) (h07 : CatalogueCentralizerFacts)
    (h08 : AlternatingStandardFormInputs)
    (h09 : CFSG.ComponentClassification.GSThmB.Solomon2AnInput)
    (h10 : CharTwoLieStandardFormInputs) (h11 : HNRecognitionInputs)
    (h12 : ComponentTheoryLiterature) (h13 : Solomon78StandardFormLiterature)
    (h14 : FischerThompsonRowInputs) (h15 : TwoFi22RecognitionInputs)
    (h16 : OddStandardL34HeChildren)
    (hGH74 : type_of% @CFSG.Milestones.cl_lit_gh74_sectional_two_rank_four_models)
    (hCIT : type_of% @CFSG.Milestones.cl_lit_classical_involution_theorem_models)
    (hCTE : Induction.CTEvenResidualStatement) :
    Frontier.OrderStatement :=
  Frontier.ctss_order_of_frontier'
    (h01.fs79 h01.kdnp hCIT hGH74 hCTE (h16.l34 hCIT hGH74) (h16.he hCIT))
    h07.catZ2A6 HSStd.Zassenhaus.A6A6.prop21A6A6Case_proved h07.catZ2A7 h02.egawaHypA
    h02.harrisSolomon h07.catM10 h04.outerS16Loc h04.outerS84 h05.harada39One h05.harris311
    h05.harris311HiS h07.kgA6Sq h06.onan77S5 h06.onanNoSL29Y h07.catE16 h06.onanInspection
    h07.kgHS3
    (CFSG.ComponentClassification.RankTwoSporadic.HS.sporadicCaseOdd_HS
      CFSG.ComponentClassification.RankTwoFoundation.lemma32
      CFSG.ComponentClassification.RankTwoFoundation.lemma33Three)
    h03.kgPumpTableT h08.altStdFormBigStd (TwoHS.GH312.gh312Fixed_of_gh74 hGH74)
    (CFSG.SeitzReduction.seitzExclusion_highPSL_of_final11_gls3
      CFSG.SeitzReduction.LinearPilot.lFiveFieldTildeSplitInput_holds)
    h05.harada39Two
    (sol78LitCore_of_yardstones (citPart2_of_models hCIT) (h16.l34 hCIT hGH74) (h16.he hCIT) hCTE
      Induction.ctEvenSmallLieStatement_of_milestone h12 h13)
    h09
    h03.noFixedDoubleCover h11.haradaHN
    (Induction.Balance.StdUHered.of_catalog
      CFSG.ComponentClassification.FooteLit.catalogAlmostSimpleUnbalancedOutcome_holds)
    h05.ghLemma53_1
    (h10.thm54 (citPart2_of_models hCIT) hCTE)
    h14.hypOneFi24 h14.thSylowWreathPair h01.co2 h15.fi24Local hGH74
    h07.ds81Lemma210Two h14.fi22Covers h14.u62Covers
    (h14.u62OddExcl (citPart2_of_models hCIT))

end Certified

end CFSG.Yardstones.M1442643da6f2
