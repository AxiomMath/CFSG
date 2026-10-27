module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveEightEmptyWASTimSplitASClaims
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveGapSixHolds
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveRootRankL2Holds
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveRootRankU3Holds
public import CFSG.LocalAnalysis.WeakClosure81.SevenNineOrthHolds
public import CFSG.LocalAnalysis.WeakClosure81.EightTailAssembly
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPFiniteL2
import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPSchur

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.RankThreeUC


theorem ascTwelveEightEmptyW_of_inputs_AS_tail
    (hC : ∀ (G : Type) [Group G] [Finite G], Standing G → AGL81TheoremC G)
    (h5_11 : WeakClosure81.Asch5_11AS) (h5_13 : WeakClosure81.Asch5_13AS)
    (hF0 : WeakClosure81.OddSchurMultiplierFact)
    (hF1 : WeakClosure81.InvolutionCentralizerFact)
    (hF2 : WeakClosure81.FourGroupInnerFact)
    (hF3 : WeakClosure81.BorelOvergroupFact)
    (hF4 : WeakClosure81.ChoiceOfKFact)
    (hF6 : WeakClosure81.BorelGL32Fact)
    (h93 : ∀ (G : Type) [Group G] [Finite G] (V T : Subgroup G), WeakClosure81.Thm93Syl V T)
    (hTI : WeakClosure81.TimmesfeldTIRootInput)
    (hCore : WeakClosure81.OddTranspositionCoreInputSC)
    (hList : WeakClosure81.OddTranspListBundle)
    (hLie : WeakClosure81.SpPSULieFacts)
    (hRU : WeakClosure81.SevenK.UnitaryRootCommutatorRank) :
    CFSG.Yardstones.Me2c15c2c995a.AscTwelveEightEmptyW := by
  have hP : ∀ (G : Type) [Group G] [Finite G], WeakClosure81.W3Lem85ThreeFirst G ∧
      WeakClosure81.W3Shape86C G ∧ WeakClosure81.W3Borel86 G := fun G _ _ =>
    WeakClosure81.w3Lem85ThreeFirst_and_shape_of_producers hLie
      (WeakClosure81.w3Lem711Alt_subgroups_of_inputs hTI
        (CFSG.LocalAnalysis.WeakClosure81.SevenK.twoConjugateGeneration_of_suzukiSubgroupInput
            LieType.SuzukiSubgroups.suzukiSubgroupInput_holds)
        (fun K _ _ => WeakClosure81.A6Case.sevenElevenASixInput_holds K) hCore hList
        (fun K _ _ => WeakClosure81.SzExcl.sevenSevenTwoInput_holds K)
        WeakClosure81.orthReflParabolic_holds)
      hRU WeakClosure81.l2IrreducibleRank_holds WeakClosure81.orth6MinusOddTranspFact_holds
      WeakClosure81.spURootConfiguration_holds
  exact ascTwelveEightEmptyW_of_inputs_AS_tim_split_claims_AS_finite_facts_at3 hC h5_11 h5_13 hF0
      hF1 hF2 hF3 hF4 hF6 h93 hTI hCore hList WeakClosure81.orthReflParabolic_holds
      (WeakClosure81.unitaryRootCommutatorRankAt_three_of_irreducible
          WeakClosure81.su3IrreducibleRank_holds) WeakClosure81.l2IrreducibleRank_holds
      WeakClosure81.orth6MinusOddTranspFact_holds (fun G _ _ => (hP G).1) (fun G _ _ => (hP G).2.1)

theorem ascTwelveEightEmptyW_of_inputs_AS_tail_shapes
    (hC : ∀ (G : Type) [Group G] [Finite G], Standing G → AGL81TheoremC G)
    (h5_11 : WeakClosure81.Asch5_11AS) (h5_13 : WeakClosure81.Asch5_13AS)
    (hCS : WeakClosure81.CitedShapeFacts) (hGS : WeakClosure81.GapShapeFacts)
    (h93 : ∀ (G : Type) [Group G] [Finite G] (V T : Subgroup G), WeakClosure81.Thm93Syl V T)
    (hTI : WeakClosure81.TimmesfeldTIRootInput)
    (hCore : WeakClosure81.OddTranspositionCoreInputSC)
    (hList : WeakClosure81.OddTranspListBundle)
    (hLie : WeakClosure81.SpPSULieFacts)
    (hRU : WeakClosure81.SevenK.UnitaryRootCommutatorRank) :
    CFSG.Yardstones.Me2c15c2c995a.AscTwelveEightEmptyW :=
  have hF := WeakClosure81.finiteFacts_of_shapes hCS hGS
  ascTwelveEightEmptyW_of_inputs_AS_tail hC h5_11 h5_13
    (WeakClosure81.oddSchurMultiplierFact_of_griess
      CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement)
    hF.1 hF.2.1 hF.2.2.1 hF.2.2.2.1 hF.2.2.2.2 h93 hTI hCore hList hLie hRU

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
