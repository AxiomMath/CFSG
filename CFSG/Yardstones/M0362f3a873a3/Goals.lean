module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Wire.Top
public import CFSG.LocalAnalysis.EvenSporadicStandard.Frontier.HSSection5Lit
public import CFSG.Yardstones.M1442643da6f2.Goals
public import CFSG.Yardstones.M1442643da6f2.Reduction
public import CFSG.Milestones.CTSS_sporadic_standard_centerless_M12_J2_and_other_quotients_frontier
public import CFSG.LocalAnalysis.OddStandard.HigherRank.OfYamada
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YCoreHolds
public import CFSG.Milestones.CL_LIT_Gorenstein_Walter_L_balance

public section

namespace CFSG.Yardstones.M0362f3a873a3

theorem altStdBalancedOrder2InnerSmall_holds :
    CFSG.OddStandard.AltStdSec.AltStdBalancedOrder2InnerSmall :=
  CFSG.OddStandard.AltStdSmall4.CTOdd.altStdBalancedOrder2InnerSmall_holds

theorem shapeTwoSmallNine_holds :
    CFSG.OddStandard.AltStdSec.ShapeTwoSmallNine :=
  CFSG.OddStandard.AltStdSmall4.CTOdd.shapeTwoSmallNine_holds

theorem shapeTwoTenNoSwapPartnerNoCentral_holds :
    CFSG.OddStandard.AltStdSec.ShapeTwoTenNoSwapPartnerNoCentralStdHS :=
  CFSG.OddStandard.AltStdSec.shapeTwoTenNoSwapPartnerNoCentralStdHS_of_inputs
    CFSG.SeitzReduction.gls3OddLieAutComponentsInput
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
    CFSG.OddStandard.AltStdSec.shapeTwoTenL44Excl_holds

theorem shapeTwoTenSwapPartnerStdHS_holds :
    CFSG.OddStandard.AltStdSec.ShapeTwoTenSwapPartnerStdHS :=
  CFSG.OddStandard.AltStdSec.SwapPartner.shapeTwoTenSwapPartnerStdHS_of_frames
    CFSG.OddStandard.AltStdSec.SwapPartner.ys04a_holds
    CFSG.OddStandard.AltStdSec.SwapPartner.ys04b_holds

theorem hsSection5_holds :
    CFSG.EvenSporadicStandard.HSStd.HSSection5 :=
  CFSG.EvenSporadicStandard.Frontier.hsSection5_of_sol78LitCore
    CFSG.Yardstones.M1442643da6f2.involutionCentralizerTheorems_holds
    CFSG.Yardstones.M1442643da6f2.onanInputs_holds
    CFSG.Yardstones.M1442643da6f2.hnRecognitionInputs_holds
    (CFSG.Yardstones.M1442643da6f2.sol78LitCore_of_yardstones
      (CFSG.Yardstones.M1442643da6f2.citPart2_of_models
        CFSG.Milestones.cl_lit_classical_involution_theorem_models)
      (CFSG.Yardstones.M1442643da6f2.oddStandardL34HeChildren_holds.l34
        CFSG.Milestones.cl_lit_classical_involution_theorem_models
        CFSG.Milestones.cl_lit_gh74_sectional_two_rank_four_models)
      (CFSG.Yardstones.M1442643da6f2.oddStandardL34HeChildren_holds.he
        CFSG.Milestones.cl_lit_classical_involution_theorem_models)
      CFSG.EvenSporadicStandard.Induction.ctEvenResidualStatement_of_milestone
      CFSG.EvenSporadicStandard.Induction.ctEvenSmallLieStatement_of_milestone
      CFSG.Yardstones.M1442643da6f2.componentTheoryLiterature_holds
      CFSG.Yardstones.M1442643da6f2.solomon78StandardFormLiterature_holds)
    (CFSG.Yardstones.M1442643da6f2.citPart2_of_models
      CFSG.Milestones.cl_lit_classical_involution_theorem_models)

theorem haradaHNRecognition_holds :
    CFSG.EvenSporadicStandard.TwoHS.HaradaHNRecognitionKP :=
  CFSG.EvenSporadicStandard.HNRecog.haradaHNRecognitionKP_holds

theorem gh312Fixed_holds :
    CFSG.EvenSporadicStandard.TwoHS.GH312Fixed :=
  CFSG.EvenSporadicStandard.TwoHS.GH312.gh312Fixed_of_gh74
    (fun G _ _ _ hnonab hrank hsect =>
      CFSG.Milestones.cl_lit_gh74_sectional_two_rank_four_models G hnonab hrank hsect)

theorem harris82Theorem1SimpleKProperOdd_holds :
    CFSG.ComponentClassification.HarrisLit.Harris82Theorem1SimpleKProperOdd :=
  CFSG.ComponentClassification.HarrisLit.harris82Theorem1SimpleKProperOdd_of_row
    (CFSG.ComponentClassification.HarrisLit.T1.harris82Theorem1KProper_of_ci
      CFSG.Milestones.cl_lit_classical_involution_theorem_models)
    CFSG.ComponentClassification.HarrisLit.harris82SporadicRow

theorem smallF3StandardOddLie_holds :
    CFSG.Yardstones.M0362f3a873a3.SmallF3StandardOddLieU :=
  CFSG.OddStandard.SmallF3.smallF3StandardOddLieU_of_leaves
    CFSG.Milestones.ctss_sporadic_standard_centerless_m12_j2_and_other_quotients_frontier_models
    CFSG.Yardstones.M0362f3a873a3.hsSection5_holds

theorem oddLieThm187bResidualL2Ree_holds :
    OddLieThm187bResidualL2Ree :=
  oddLieThm187bResidualL2Ree_of_halves
    (CFSG.OddStandard.L2Ree.l2Half_of_milestones
      CFSG.Milestones.cl_lit_gh74_sectional_two_rank_four_models
      CFSG.Milestones.cl_lit_classical_involution_theorem_models)
    (CFSG.OddStandard.L2Ree.ree_half CFSG.EvenSporadicStandard.J1Std.walterAbelian_of_milestone
      CFSG.HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement
      CFSG.TauCetiBridge.typewiseBridges)

theorem oddLieThm187bResidualHigherRank_holds :
    OddLieThm187bResidualHigherRank :=
  CFSG.OddStandard.HigherRank.oddLieThm187bResidualHigherRank_of_yamadaCase3Core
    CFSG.Milestones.cl_lit_classical_involution_theorem_models
    (CFSG.OddStandard.Solomon75.solomon2AnInput_of_gh74Milestone
      @CFSG.Milestones.cl_lit_gh74_sectional_two_rank_four_models)
    (fun X _ _ hK p hp P hP => CFSG.Milestones.cl_lit_gorenstein_walter_l_balance X hK p hp P hP)
    CFSG.OddStandard.HigherRank.YamadaG23.yamadaCase3Core_holds

theorem heldKSwapped_holds :
    CFSG.ComponentClassification.GrSLit.HeldKSwapped :=
  CFSG.ComponentClassification.GrSLit.heldKSwapped_of_cit
    CFSG.Milestones.cl_lit_classical_involution_theorem_models
    (CFSG.ComponentClassification.Sol76.Sig.lemma315bInputFor_simple_of_hbK2Leaves
      CFSG.ComponentClassification.Sol76.Sig.GSYard03.lemma39TwoDiscK2At_solRestrictedHub_holds
      CFSG.ComponentClassification.Sol76.Sig.GSYard02.quasisimpleSylowFourJoinedSCN_holds
      CFSG.ComponentClassification.Sol76.Sig.GSYard03.solomonQTwoDisconnectedSylowInvFor_holds)

end CFSG.Yardstones.M0362f3a873a3
