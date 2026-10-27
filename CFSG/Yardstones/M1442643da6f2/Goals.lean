module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpTableHolds
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.NoFixedDoubleCoverHolds
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentralizerFacts
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.DS81EvenHolds
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Exclusion.KDM22Proof.Holds
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Exclusion.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.OuterCaseFields
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RFinal
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8Final
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.KD.Eight
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.KD.Small
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Ega81K
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.HoldsClosed
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.GHLemma53One
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.Final
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.FinalTwo
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harris.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.NoFifteen
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.OutNoOdd
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.HaradaOne
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.HaradaTwo
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Harris
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.HarrisHiS
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.Cat3.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.Inspection
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.NoSL29
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.S5Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm54Reach.Concrete
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm54Reach.Hered
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm46FS.L3Ge3
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm46FS.L34Supp
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdCatSuzHolds
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm46FS.G2Supp
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm46FS.Hered
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm46FS.SuzEven
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm46FS.G2EvenOuterHolds
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm46FS.Co1G24CentreHolds
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm46FS.SporL34CentreHolds
public import CFSG.LocalAnalysis.OddStandard.AltStdFormBigStd
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm46FS.OddChildren
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm46FS.OddChildrenHered
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaHNHolds
public import CFSG.LocalAnalysis.EvenSporadicStandard.YS14.AssemblyHard
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.SylowWreathPair
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Holds
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.U62CoversFinal
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.U62Odd.Hered

public section

namespace CFSG.Yardstones.M1442643da6f2

theorem conwayStandardInputs_holds :
    ConwayStandardInputs :=
  ⟨CFSG.EvenSporadicStandard.M12Std.Rbc.fs79RbcHered_holds
      CFSG.ComponentClassification.FooteLit.catalogAlmostSimpleUnbalancedOutcome_holds,
    And.intro CFSG.EvenSporadicStandard.M12Std.Rbc.kdnpSmall_holds
      CFSG.EvenSporadicStandard.M12Std.Rbc.kdnpEight_holds,
    CFSG.EvenSporadicStandard.Co2Std.Exclusion.co2Exclusion_of_kdm22
      CFSG.EvenSporadicStandard.Co2Std.Exclusion.kdm22_holds⟩

theorem egawaHarrisSolomonInputs_holds :
    EgawaHarrisSolomonInputs :=
  ⟨CFSG.EvenSporadicStandard.M24Std.ega81HypAZ2A8K_holds,
    CFSG.EvenSporadicStandard.M24Std.harrisSolomonZ2S6IsoK_proved⟩

theorem catalogueFixedComponentFacts_holds :
    CatalogueFixedComponentFacts :=
  ⟨CFSG.ComponentClassification.CatFC.kgPumpTableT_holds,
    CFSG.ComponentClassification.CatFC.catalogNoFixedDoubleCover_holds⟩

theorem finkelstein76bOuterCase_holds :
    Finkelstein76bOuterCase :=
  finkelstein76bOuterCase_of_fields CFSG.EvenSporadicStandard.Fin76b.fin76bOuterS16Loc_holds
    CFSG.EvenSporadicStandard.Fin76b.outerS84_holds

theorem involutionCentralizerTheorems_holds :
    InvolutionCentralizerTheorems :=
  ⟨CFSG.EvenSporadicStandard.HSStd.InvCent.harada39One_of_cat
      CFSG.EvenSporadicStandard.HSStd.InvCent.catHaradaAS_holds,
    CFSG.EvenSporadicStandard.HSStd.InvCent.harada39Two_of_cat
      CFSG.EvenSporadicStandard.HSStd.InvCent.catHaradaTwoAS_holds
      CFSG.EvenSporadicStandard.HSStd.InvCent.catCentFour_holds,
    CFSG.EvenSporadicStandard.HSStd.InvCent.harris311_of_cat
      CFSG.EvenSporadicStandard.HSStd.InvCent.Harris.catHarrisAS_holds,
    CFSG.EvenSporadicStandard.HSStd.InvCent.harris311HiS_of_cat
      CFSG.EvenSporadicStandard.HSStd.InvCent.Harris.catHarrisAS_holds
      CFSG.EvenSporadicStandard.HSStd.InvCent.noFifteen_holds
      CFSG.EvenSporadicStandard.HSStd.InvCent.outNoOdd_holds,
    CFSG.EvenSporadicStandard.RuStd.S2.ghLemma53_1_holds⟩

theorem onanInputs_holds :
    ONanInputs :=
  ⟨CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan.S5.onan77S5_of_catThreeA5
      CFSG.RankThree.PartOne.SPOR.schreierFor_catalog
      CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan.Cat3.catThreeA5_holds,
    CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan.onanInspection_holds,
    CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan.onanNoSL29Y_holds⟩

theorem catalogueCentralizerFacts_holds :
    CatalogueCentralizerFacts :=
  CFSG.ComponentClassification.CatFC.catalogueCentralizerFacts_of_ds81Even
    CFSG.ComponentClassification.CatFC.DS81.ds81EvenLie_holds

theorem alternatingStandardFormInputs_holds :
    AlternatingStandardFormInputs :=
  ⟨CFSG.OddStandard.AltStdSec.altStdFormBigStd_holds⟩

theorem solomon2AnInput_holds :
    CFSG.ComponentClassification.GSThmB.Solomon2AnInput :=
  CFSG.OddStandard.Solomon75.solomon2AnInput_of_gh74Milestone
    @CFSG.Milestones.cl_lit_gh74_sectional_two_rank_four_models

theorem charTwoLieStandardFormInputs_holds :
    CharTwoLieStandardFormInputs :=
  ⟨fun hCIT hCTE =>
    CFSG.EvenSporadicStandard.Induction.Thm54Reach.sol78Thm54ReachHered_of_inputs
      CFSG.EvenSporadicStandard.Induction.Thm54Reach.catInputs_holds
      CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer.rankTwoStdRec_proved
      (CFSG.EvenSporadicStandard.Induction.sol78Thm24_1Use_of_citPart2 hCIT) hCTE
      CFSG.EvenSporadicStandard.Induction.Thm54Reach.excInput_holds⟩

theorem hnRecognitionInputs_holds :
    HNRecognitionInputs :=
  ⟨CFSG.EvenSporadicStandard.HNRecog.haradaHNRecognitionKP_holds⟩

theorem componentTheoryLiterature_holds :
    ComponentTheoryLiterature :=
  ⟨fun H _ _ hH =>
    CFSG.EvenSporadicStandard.Induction.fs79Thm13UseAt_of_lemma15At
      (CFSG.EvenSporadicStandard.Induction.fs79Lemma15At_of_uhered H hH)⟩

theorem solomon78StandardFormLiterature_holds :
    Solomon78StandardFormLiterature :=
  ⟨fun hCIT hChL34 hChHe hCTE hSmall =>
    CFSG.EvenSporadicStandard.Induction.sol78Thm46FSHered_of_inputs
      CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer.rankTwoStdRec_proved
      (CFSG.EvenSporadicStandard.Induction.sol78Thm24_1Use_of_citPart2 hCIT)
      (fun _ _ hge hHe =>
        CFSG.EvenSporadicStandard.Induction.Thm54Reach.not_evenStandardException_of_card hge
          hHe)
      hChL34 hChHe hCTE hSmall CFSG.EvenSporadicStandard.Induction.thm46Orders_proved
      (CFSG.EvenSporadicStandard.Induction.suzCentralTwo_of_centralTwoBound
        CFSG.EvenSporadicStandard.centralTwoBound)
      CFSG.EvenSporadicStandard.Induction.sol78Thm46SuzEven_holds
      CFSG.ComponentClassification.GrSLit.L34Sec5S.suzONanNotProperFixedCatalog_holds
      (CFSG.ComponentClassification.CatLeaf.heldNotProperFixedInput_of_inputs'
        CFSG.SeitzReduction.gls3OddLieAutComponentsInput
        CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
        CFSG.ComponentClassification.CatLeafProof.evenLieOuterTwoComponentsInput_holds
        CFSG.ComponentClassification.CatLeafProof.monsterInnerInput
        CFSG.ComponentClassification.CatLeafProof.monsterLocalComponentsInput
        CFSG.ComponentClassification.CatalogueU.sporadicOddCoreFree_M)
      CFSG.EvenSporadicStandard.Induction.l3FixedCatalogGe3_holds
      CFSG.EvenSporadicStandard.Induction.l34FixedCatalog_holds
      CFSG.EvenSporadicStandard.Induction.sol78Thm46SporL34Centre_holds,
    fun hCIT hCTE hSmall =>
    CFSG.EvenSporadicStandard.Induction.sol78Thm412FSHered_of_inputs
      CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer.rankTwoStdRec_proved
      (CFSG.EvenSporadicStandard.Induction.sol78Thm24_1Use_of_citPart2 hCIT)
      (fun _ _ hge hHe =>
        CFSG.EvenSporadicStandard.Induction.Thm54Reach.not_evenStandardException_of_card hge
          hHe)
      hCTE hSmall CFSG.EvenSporadicStandard.Induction.thm46Orders_proved
      (CFSG.EvenSporadicStandard.Induction.g2FixedCatalog_of_outer
        CFSG.EvenSporadicStandard.Induction.g2EvenOuterFixedCatalog_holds)
      CFSG.EvenSporadicStandard.Induction.co1G24Centre_holds⟩

theorem fischerThompsonRowInputs_holds :
    FischerThompsonRowInputs :=
  CFSG.EvenSporadicStandard.YS14.fischerThompsonRowInputs_of_hard_fields
    (CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_of_openCells
      CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicOpenCells_holds)
    (CFSG.EvenSporadicStandard.Induction.Fi.u62Covers_of_griess
      CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement)
    (fun hCIT => CFSG.EvenSporadicStandard.Induction.Fi.U62Odd.u62OddExclHered_of_milestones
      hCIT)
    CFSG.EvenSporadicStandard.ThStd.thSylowWreathPair

theorem twoFi22RecognitionInputs_holds :
    TwoFi22RecognitionInputs :=
  ⟨CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.fi24RecognitionLocal_holds⟩

theorem oddStandardL34HeChildren_holds :
    OddStandardL34HeChildren :=
  ⟨fun hCIT hGH G _ _ hU =>
      CFSG.EvenSporadicStandard.Induction.childL34WAt_of_casesBal
        CFSG.OddStandard.rankTwoL3FourStandard_holds hCIT
        (CFSG.OddStandard.l34CyclicOddCenter_of_seitzSimple
          (CFSG.OddStandard.Seitz77.seitz77SimpleL34_of_gh74 hGH))
        (CFSG.OddStandard.ONanRec.l34CyclicEvenCenterBal_of_sylowStepBal'
          CFSG.OddStandard.ChengHeld.l34EvenSylowStepBal_holds
          (CFSG.OddStandard.ONanRec.sylowBal_ON_of_gh74 hGH))
        hU,
    fun hCIT G _ _ hU =>
      CFSG.EvenSporadicStandard.Induction.childHeWAt_of_casesO
        CFSG.Sporadic.Recognition.HeMultiplier.heldTrivialMultiplier_of_certificate
        (CFSG.OddStandard.rankTwoHeStandardO_of_rankTwoHeStandard
          (CFSG.OddStandard.rankTwoHeStandard_of_flat
            CFSG.ComponentClassification.RankTwoFoundation.thm5Flat))
        (CFSG.ComponentClassification.GrSLit.heStandardBalanced_of_heldKSwapped
          (CFSG.EvenSporadicStandard.Induction.heldKSwapped_of_milestones hCIT))
        hU⟩

end CFSG.Yardstones.M1442643da6f2
