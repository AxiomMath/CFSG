module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveEightEmptyWAS
public import CFSG.CGT.Timmesfeld75.FinalNodeRest
public import CFSG.CGT.A8S.Final
public import CFSG.CGT.M24S.Main
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveGapsDischarged
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveRootRankL2
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveTwoSplit
public import CFSG.LocalAnalysis.WeakClosure81.SzExcl.Main

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.RankThreeUC

theorem ascTwelveEightEmptyW_of_inputs_AS_tim_split_at3
    (hC : ∀ (G : Type) [Group G] [Finite G], Standing G → AGL81TheoremC G)
    (h5_11 : WeakClosure81.Asch5_11AS) (h5_13 : WeakClosure81.Asch5_13AS)
    (h88 : ∀ (G : Type) [Group G] [Finite G], W3Thm88 G)
    (h93 : ∀ (G : Type) [Group G] [Finite G] (V T : Subgroup G), WeakClosure81.Thm93Syl V T)
    (hTI : WeakClosure81.TimmesfeldTIRootInput)
    (hGen : WeakClosure81.SevenK.TwoConjugateGeneration)
    (hA6 : ∀ (K : Type) [Group K] [Finite K], WeakClosure81.SevenElevenASixInput K)
    (hCore : WeakClosure81.OddTranspositionCoreInputSC)
    (hList : WeakClosure81.OddTranspListBundle)
    (hIn : WeakClosure81.OrthReflParabolic)
    (hRU : WeakClosure81.UnitaryRootCommutatorRankAt 3)
    (hL2 : WeakClosure81.L2IrreducibleRank)
    (hfact : WeakClosure81.Orth6MinusOddTranspFact)
    (h85three : ∀ (G : Type) [Group G] [Finite G], WeakClosure81.W3Lem85ThreeFirst G)
    (hsh : ∀ (G : Type) [Group G] [Finite G], WeakClosure81.W3Shape86C G) :
    CFSG.Yardstones.Me2c15c2c995a.AscTwelveEightEmptyW :=
  ascTwelveEightEmptyW_of_inputs_AS hC h5_11 h5_13
      (fun G _ _ => WeakClosure81.w3Lem86_1_of_split_inputs_at3
          (WeakClosure81.w3Lem711Alt_subgroups_of_inputs hTI hGen hA6 hCore hList
              WeakClosure81.SzExcl.sevenSevenTwoInput_forall hIn) hRU
          (WeakClosure81.l2RootCommutatorRank_of_irreducible hL2) hfact (h85three G) (hsh G)) h88
      h93
      (CFSG.CGT.Timmesfeld75.node_final_rest
          ⟨CFSG.CGT.A8S.a8SylowInput, CFSG.CGT.M24S.m24SylowInput⟩)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
