module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SlotsThreeTail
public import CFSG.LocalAnalysis.WeakClosure81.W183Remaining
public import CFSG.LocalAnalysis.WeakClosure81.Asc80BMain
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPCited
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1SixProof
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen5KThreeInnerHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67CentL3U3Holds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67OuterInvL3U3Holds
public import CFSG.LocalAnalysis.WeakClosure81.SpUCitedHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.KSeven.Cases
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSp6SmallFinal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8H1Eight
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSp6H1Final
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1R925RestHolds
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

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7






theorem ascSixteenSixtyNine_of_inputs_tail_noShapes
    (hC : ∀ (G : Type) [Group G] [Finite G], RankThreeUC.Standing G →
      RankThreeUC.AGL81TheoremC G)
    (hin : Inputs1669Three) :
    CFSG.Yardstones.Me2c15c2c995a.AscSixteenSixtyNine :=
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
  ascSixteenSixtyNine_of_inputs_tail WeakClosure81.asch5_4_holds WeakClosure81.asch5_12_holds h136
    (StronglyEmbeddedThreeKIB_of_small
      CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.gls3StronglyThreeEmbeddedPlus_holds
      KIB3Small_holds)
    Seven.ksevenGen_holds
    kThreeInner_holds
    Small.k67CentL3U3_holds Small.k67OuterInvL3U3_holds
    (oddIdxPropL3U3_of_rest oddIdxPropL3U3Rest_holds) hC
    WeakClosure81.citedShapeFacts_holds WeakClosure81.timmesfeldTIRootInput_holds hCore hList
    WeakClosure81.spPSULieFacts_holds
    (WeakClosure81.w3Thm183_of_remaining_inputs hB hCore hList
      WeakClosure81.oddTranspositionCompFactorInput_holds)
    (fun _ _ _ => WeakClosure81.w3Thm193_of_cited hB hCore hList)
    (fun _ _ _ => WeakClosure81.w3Thm162Ext_of_cited hB hCore hList)
    h139 (rSp6SmallMod_holds fun V _ _ _ ρ hρ h8 => finrank_H1_irreducible_eight V ρ hρ h8)
    (rSp6SpinCent_holds rSp6SpinUnique_holds) (rSp6SpinForm_holds rSp6SpinUnique_holds)
    (rSp6SpinStab_holds rSp6SpinUnique_holds) h1SpSixNatural_holds
    s1611e3_v1_six_gap_holds hin

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three

end
