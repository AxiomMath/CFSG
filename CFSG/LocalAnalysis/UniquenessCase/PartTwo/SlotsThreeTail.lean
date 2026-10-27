module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SlotsThreeAssembly
public import CFSG.LocalAnalysis.WeakClosure81.EightEightPFinalAS
public import CFSG.LocalAnalysis.WeakClosure81.EightTailAssembly
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeT79Main
public import CFSG.LocalAnalysis.WeakClosure81.SevenKUnitaryHolds
import CFSG.LocalAnalysis.WeakClosure81.A6Case.Main
import CFSG.LieType.SuzukiSubgroups.Input
import CFSG.LocalAnalysis.WeakClosure81.TwoConjugateSzProof
import CFSG.LocalAnalysis.WeakClosure81.EightFiveRootRankL2Holds
import CFSG.LocalAnalysis.WeakClosure81.EightFiveGapSixHolds
import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapFinal
public import CFSG.LocalAnalysis.WeakClosure81.SzExcl.Main

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7




theorem ascSixteenSixtyNine_of_inputs_tail
    (h54 : WeakClosure81.Asch5_4)
    (h512 : WeakClosure81.Asch5_12)
    (h136 : W4Lem13_6) (hKIB : StronglyEmbeddedThreeKIB)
    (hKA : KSevenGen) (hKB : KThreeInner)
    (hL3Cent : Small.K67CentL3U3) (hL3Out : Small.K67OuterInvL3U3) (hL3U3 : OddIdxPropL3U3)
    (hC : ∀ (G : Type) [Group G] [Finite G], RankThreeUC.Standing G →
      RankThreeUC.AGL81TheoremC G)
    (hCS : WeakClosure81.CitedShapeFacts)
    (hTI : WeakClosure81.TimmesfeldTIRootInput)
    (hCore : WeakClosure81.OddTranspositionCoreInputSCCls)
    (hList : WeakClosure81.OddTranspListBundleCls)
    (hLie : WeakClosure81.SpPSULieFacts)
    (h183 : ∀ (G : Type) [Group G] [Finite G], W3Thm183 G)
    (h193 : ∀ (G : Type) [Group G] [Finite G], W3Thm193 G)
    (h162 : ∀ (G : Type) [Group G] [Finite G], W3Thm162Ext G) (h139 : WeakClosure81.Hyp139)
    (hSpA : RSp6SmallMod) (hSpC : RSp6SpinCent) (hSpF : RSp6SpinForm)
    (hSpSt : RSp6SpinStab) (hH1 : H1SpSixNatural) (hGap : S1611e3V1SixGap)
    (hin : Inputs1669Three) :
    CFSG.Yardstones.Me2c15c2c995a.AscSixteenSixtyNine := by
  have hRU : WeakClosure81.SevenK.UnitaryRootCommutatorRank :=
    WeakClosure81.unitaryRootCommutatorRank_holds
  have h5_11 : WeakClosure81.Asch5_11AS := WeakClosure81.asch5_11AS_of_remaining_inputs h54
  have h5_13 : WeakClosure81.Asch5_13AS :=
    WeakClosure81.asch5_13AS_of_inputs h512 WeakClosure81.asch4_11ASPow_holds
  have hA6 : ∀ (K : Type) [Group K] [Finite K], WeakClosure81.SevenElevenASixInput K :=
    fun K _ _ => WeakClosure81.A6Case.sevenElevenASixInput_holds K
  have h772 : ∀ (K : Type) [Group K] [Finite K], WeakClosure81.SevenSevenTwoInput K :=
    fun K _ _ => WeakClosure81.SzExcl.sevenSevenTwoInput_holds K
  have h711 : ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G),
      WeakClosure81.W3Lem711Alt ↥H := fun G _ _ =>
    WeakClosure81.w3Lem711Alt_subgroups_of_inputs hTI
      (CFSG.LocalAnalysis.WeakClosure81.SevenK.twoConjugateGeneration_of_suzukiSubgroupInput
          LieType.SuzukiSubgroups.suzukiSubgroupInput_holds) hA6 hCore.toInput
      hList.toInput h772 WeakClosure81.orthReflParabolic_holds
  have h861 : ∀ (G : Type) [Group G] [Finite G], W3Lem86_1 G := by
    intro G _ _
    have hP := WeakClosure81.w3Lem85ThreeFirst_and_shape_of_producers (G := G) hLie (h711 G)
      hRU WeakClosure81.l2IrreducibleRank_holds WeakClosure81.orth6MinusOddTranspFact_holds
      WeakClosure81.spURootConfiguration_holds
    exact WeakClosure81.w3Lem86_1_of_split_inputs (h711 G) hRU
      (WeakClosure81.l2RootCommutatorRank_of_irreducible WeakClosure81.l2IrreducibleRank_holds)
      WeakClosure81.orth6MinusOddTranspFact_holds hP.1 hP.2.1
  have h88 : ∀ (G : Type) [Group G] [Finite G], W3Thm88 G := by
    intro G _ _ V H T i h
    have hP := WeakClosure81.w3Lem85ThreeFirst_and_shape_of_producers (G := G) hLie
      (WeakClosure81.w3Lem711Alt_subgroups_of_inputs hTI
        (CFSG.LocalAnalysis.WeakClosure81.SevenK.twoConjugateGeneration_of_suzukiSubgroupInput
            LieType.SuzukiSubgroups.suzukiSubgroupInput_holds) hA6 hCore.toInput
        hList.toInput h772 WeakClosure81.orthReflParabolic_holds)
      hRU WeakClosure81.l2IrreducibleRank_holds WeakClosure81.orth6MinusOddTranspFact_holds
      WeakClosure81.spURootConfiguration_holds
    exact WeakClosure81.w3Thm88_of_split_inputs'_AS
      CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement hCS
      WeakClosure81.gapShapeFacts_holds hTI
      (CFSG.LocalAnalysis.WeakClosure81.SevenK.twoConjugateGeneration_of_suzukiSubgroupInput
          LieType.SuzukiSubgroups.suzukiSubgroupInput_holds) hA6 hCore.toInput hList.toInput
      h772 WeakClosure81.orthReflParabolic_holds hRU
      (WeakClosure81.l2RootCommutatorRank_of_irreducible WeakClosure81.l2IrreducibleRank_holds)
      WeakClosure81.orth6MinusOddTranspFact_holds hP.1 hP.2.1 h5_11 h5_13 h
  exact ascSixteenSixtyNine_of_inputs h54 h512 h136 hKIB hKA hKB hL3Cent hL3Out hL3U3 hC
    h861 h88 (fun _ _ _ _ _ => WeakClosure81.thm93Syl_of_classification hCore hList h772)
    h183 h193 h162 h139 hSpA hSpC hSpF hSpSt hH1 hGap hin

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three

end
