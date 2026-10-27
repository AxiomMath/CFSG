module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPMain
public import CFSG.LocalAnalysis.WeakClosure81.EightNineteenPProof
public import CFSG.LocalAnalysis.WeakClosure81.EightTwentyPProof
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveEightEmptyWASTimSplit
public import CFSG.LocalAnalysis.WeakClosure81.EightEightPAS
public import CFSG.LieType.SuzukiSubgroups.Input
public import CFSG.LocalAnalysis.WeakClosure81.TwoConjugateSzProof
public import CFSG.LocalAnalysis.WeakClosure81.A6Case.Main

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.RankThreeUC

theorem ascTwelveEightEmptyW_of_inputs_AS_tim_split_claims_AS_finite_facts_at3
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
    (hIn : WeakClosure81.OrthReflParabolic)
    (hRU : WeakClosure81.UnitaryRootCommutatorRankAt 3)
    (hL2 : WeakClosure81.L2IrreducibleRank)
    (hfact : WeakClosure81.Orth6MinusOddTranspFact)
    (h85three : ∀ (G : Type) [Group G] [Finite G], WeakClosure81.W3Lem85ThreeFirst G)
    (hsh : ∀ (G : Type) [Group G] [Finite G], WeakClosure81.W3Shape86C G) :
    CFSG.Yardstones.Me2c15c2c995a.AscTwelveEightEmptyW :=
  ascTwelveEightEmptyW_of_inputs_AS_tim_split_at3 hC h5_11 h5_13
    (fun G _ _ => WeakClosure81.w3Thm88_of_split_claims'_discharged_AS_at3
      (WeakClosure81.w3Lem813''_holds h5_11 h5_13 hF0 hF1 hF2 hF3 hF4)
      (WeakClosure81.w3Claim819'_holds h5_11 h5_13 hF0 hF1 hF2 hF3)
      (WeakClosure81.w3Claim820'_holds h5_11 h5_13 hF0 hF1 hF2 hF3 hF6)
      hTI (CFSG.LocalAnalysis.WeakClosure81.SevenK.twoConjugateGeneration_of_suzukiSubgroupInput
        CFSG.LieType.SuzukiSubgroups.suzukiSubgroupInput_holds)
      (fun K _ _ => WeakClosure81.A6Case.sevenElevenASixInput_holds K) hCore hList
      WeakClosure81.SzExcl.sevenSevenTwoInput_forall hIn hRU
      (WeakClosure81.l2RootCommutatorRank_of_irreducible hL2) hfact (h85three G) (hsh G)
      h5_11 h5_13)
    h93 hTI (CFSG.LocalAnalysis.WeakClosure81.SevenK.twoConjugateGeneration_of_suzukiSubgroupInput
        CFSG.LieType.SuzukiSubgroups.suzukiSubgroupInput_holds)
    (fun K _ _ => WeakClosure81.A6Case.sevenElevenASixInput_holds K)
    hCore hList hIn hRU hL2 hfact h85three hsh

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
