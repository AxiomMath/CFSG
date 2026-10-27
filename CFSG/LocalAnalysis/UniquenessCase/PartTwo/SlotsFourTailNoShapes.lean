module

public import CFSG.LocalAnalysis.WeakClosure81.W183Remaining
public import CFSG.LocalAnalysis.WeakClosure81.Asc80BMain
import CFSG.LocalAnalysis.UniquenessCase.UC7P3ThreeKIBA6
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPCited
public import CFSG.LocalAnalysis.WeakClosure81.SpUCitedHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKOm8Holds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8SpinHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8CuUnique
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSp6H1Final
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKEndF2Holds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKOutM22Holds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKU43Holds
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139Main
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenSix.FourDefs
public import CFSG.LocalAnalysis.WeakClosure81.OddTranspListTriHolds
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps107Fin
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135Main
import CFSG.LocalAnalysis.WeakClosure81.OddTranspCompFactorHolds
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136Main
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrMainN
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13FourCases
import CFSG.LocalAnalysis.WeakClosure81.TrialityCentralHolds
import CFSG.LocalAnalysis.WeakClosure81.TrialityMarkedHolds
import CFSG.LocalAnalysis.WeakClosure81.OddTranspCoreSimpleHolds
import CFSG.LocalAnalysis.WeakClosure81.OddTranspCoreRadicalHolds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.FourHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SlotsFourAssembly
public import CFSG.LocalAnalysis.WeakClosure81.EightEightPFinalAS
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeT79Main
public import CFSG.LocalAnalysis.WeakClosure81.SevenKUnitaryHolds
import CFSG.LocalAnalysis.WeakClosure81.EightFiveRootRankL2Holds
import CFSG.LocalAnalysis.WeakClosure81.EightFiveGapSixHolds
import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapFinal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Four

open Subgroup CFSG.Open CFSG.Yardstones.Mf4cdcdf2e013 CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7





theorem theorem1669Four_of_inputs_tail_noShapes



















































    : Theorem1669Four := by
  have hCore : WeakClosure81.OddTranspositionCoreInputSCCls :=
    WeakClosure81.oddTranspositionCoreInputSCCls_of_cases
        (WeakClosure81.oddTranspCoreThreeTranspInput_of_simple
            WeakClosure81.oddTranspCoreSimpleInput_holds)
        WeakClosure81.oddTranspCoreRadicalInput_holds
  have hList : WeakClosure81.OddTranspListBundleCls :=
    ⟨WeakClosure81.oddTranspositionListInputClsTri_holds,
      WeakClosure81.trialityMarkedInput_holds, WeakClosure81.trialityCentralInput_holds⟩
  have h105 : Inputs1719.W4Lem10_5Four := Inputs1719.w4Lem10_5Four_holds
  have h135 : Inputs1719.W4Lem13_5 :=
    WeakClosure81.w4Lem13_5_of_inputs h105 WeakClosure81.w4Lem10_7Fin_holds
  have h139 : WeakClosure81.Hyp139 :=
    WeakClosure81.GF2Reps139.hyp139_of_inputs_closed
      (WeakClosure81.w4Lem13_4_of
        CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement)
      h135
  have h136 : W4Lem13_6 :=
    WeakClosure81.GF2Reps136.w4Lem13_6_of_inputs WeakClosure81.w4Lem13_3N_holds
      (WeakClosure81.w4Lem13_4_of
        CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement)
      h135
  have hB : WeakClosure81.Asc80ThmB := WeakClosure81.asc80ThmB_holds
  have hRU : WeakClosure81.SevenK.UnitaryRootCommutatorRank :=
    WeakClosure81.unitaryRootCommutatorRank_holds
  have h5_11 : WeakClosure81.Asch5_11AS := WeakClosure81.asch5_11AS_of_remaining_inputs WeakClosure81.asch5_4_holds
  have h5_13 : WeakClosure81.Asch5_13AS :=
    WeakClosure81.asch5_13AS_of_inputs WeakClosure81.asch5_12_holds WeakClosure81.asch4_11ASPow_holds
  have hA6 : ∀ (K : Type) [Group K] [Finite K], WeakClosure81.SevenElevenASixInput K :=
    fun K _ _ => WeakClosure81.A6Case.sevenElevenASixInput_holds K
  have h772 : ∀ (K : Type) [Group K] [Finite K], WeakClosure81.SevenSevenTwoInput K :=
    fun K _ _ => WeakClosure81.SzExcl.sevenSevenTwoInput_holds K
  have h711 : ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G),
      WeakClosure81.W3Lem711Alt ↥H := fun G _ _ =>
    WeakClosure81.w3Lem711Alt_subgroups_of_inputs WeakClosure81.timmesfeldTIRootInput_holds
      (CFSG.LocalAnalysis.WeakClosure81.SevenK.twoConjugateGeneration_of_suzukiSubgroupInput
          CFSG.LieType.SuzukiSubgroups.suzukiSubgroupInput_holds) hA6 hCore.toInput
      hList.toInput h772 WeakClosure81.orthReflParabolic_holds
  have hRL : WeakClosure81.L2RootCommutatorRank :=
    WeakClosure81.l2RootCommutatorRank_of_irreducible WeakClosure81.l2IrreducibleRank_holds
  have h861 : ∀ (G : Type) [Group G] [Finite G], W3Lem86_1 G := by
    intro G _ _
    have hP := WeakClosure81.w3Lem85ThreeFirst_and_shape_of_producers (G := G) WeakClosure81.spPSULieFacts_holds (h711 G)
      hRU WeakClosure81.l2IrreducibleRank_holds WeakClosure81.orth6MinusOddTranspFact_holds
      WeakClosure81.spURootConfiguration_holds
    exact WeakClosure81.w3Lem86_1_of_split_inputs (h711 G) hRU hRL
      WeakClosure81.orth6MinusOddTranspFact_holds hP.1 hP.2.1
  have h88 : ∀ (G : Type) [Group G] [Finite G], W3Thm88 G := by
    intro G _ _ V H T i h
    have hP := WeakClosure81.w3Lem85ThreeFirst_and_shape_of_producers (G := G) WeakClosure81.spPSULieFacts_holds (h711 G)
      hRU WeakClosure81.l2IrreducibleRank_holds WeakClosure81.orth6MinusOddTranspFact_holds
      WeakClosure81.spURootConfiguration_holds
    exact WeakClosure81.w3Thm88_of_split_inputs'_AS
      CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement WeakClosure81.citedShapeFacts_holds
      WeakClosure81.gapShapeFacts_holds WeakClosure81.timmesfeldTIRootInput_holds
      (CFSG.LocalAnalysis.WeakClosure81.SevenK.twoConjugateGeneration_of_suzukiSubgroupInput
          CFSG.LieType.SuzukiSubgroups.suzukiSubgroupInput_holds) hA6 hCore.toInput hList.toInput
      h772 WeakClosure81.orthReflParabolic_holds hRU hRL
      WeakClosure81.orth6MinusOddTranspFact_holds hP.1 hP.2.1 h5_11 h5_13 h
  exact theorem1669Four_of_inputs WeakClosure81.asch5_4_holds WeakClosure81.asch5_12_holds h136 (StronglyEmbeddedThreeKIB_of_small
      CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.gls3StronglyThreeEmbeddedPlus_holds
      KIB3Small_holds) h861 h88
    (fun _ _ _ _ _ => WeakClosure81.thm93Syl_of_classification hCore hList h772)
    (WeakClosure81.w3Thm183_of_remaining_inputs hB hCore hList
      WeakClosure81.oddTranspositionCompFactorInput_holds)
    (fun _ _ _ => WeakClosure81.w3Thm193_of_cited hB hCore hList)
    (fun _ _ _ => WeakClosure81.w3Thm162Ext_of_cited hB hCore hList) h139 h1SpSixNatural_holds
    ⟨s16kEndF2Rank10_holds, s16kOutM22_holds,
      rSp6SpinCent_holds rSp6SpinUnique_holds, rSp6SpinForm_holds rSp6SpinUnique_holds,
      rSp6SpinStab_holds rSp6SpinUnique_holds, s16kU43Noncyclic3_holds⟩ s16kOmega8OutInner_holds

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Four

end
