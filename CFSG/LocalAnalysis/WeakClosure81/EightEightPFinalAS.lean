module

public import CFSG.LocalAnalysis.WeakClosure81.EightEightPAS
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPMain
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPSchur
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPFiniteL2
public import CFSG.LocalAnalysis.WeakClosure81.EightNineteenPProof
public import CFSG.LocalAnalysis.WeakClosure81.EightTwentyPProof

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (W3Thm88)

variable {G : Type} [Group G] [Finite G]


theorem w3Thm88_of_split_inputs'_AS
    (hGA : CFSG.Open.GriessAllModelsStatement) (hC : CitedShapeFacts) (hG : GapShapeFacts)
    (hTim : TimmesfeldTIRootInput)
    (hGen : TwoConjugateGeneration)
    (hA6 : ∀ (K : Type) [Group K] [Finite K], SevenElevenASixInput K)
    (hCore : OddTranspositionCoreInputSC) (hList : OddTranspListBundle)
    (h772 : ∀ (K : Type) [Group K] [Finite K], SevenSevenTwoInput K)
    (hIn : OrthReflParabolic) (hRU : UnitaryRootCommutatorRank) (hRL : L2RootCommutatorRank)
    (hfact : Orth6MinusOddTranspFact)
    (h85three : W3Lem85ThreeFirst G) (hsh : W3Shape86C G)
    (h5_11 : Asch5_11AS) (h5_13 : Asch5_13AS) : W3Thm88 G :=
  have hF0 := oddSchurMultiplierFact_of_griess hGA
  have hF := finiteFacts_of_shapes hC hG
  w3Thm88_of_split_claims'_discharged_AS
    (w3Lem813''_holds h5_11 h5_13 hF0 hF.1 hF.2.1 hF.2.2.1 hF.2.2.2.1)
    (w3Claim819'_holds h5_11 h5_13 hF0 hF.1 hF.2.1 hF.2.2.1)
    (w3Claim820'_holds h5_11 h5_13 hF0 hF.1 hF.2.1 hF.2.2.1 hF.2.2.2.2)
    hTim hGen hA6 hCore hList h772 hIn hRU hRL hfact h85three hsh h5_11 h5_13

end CFSG.LocalAnalysis.WeakClosure81

end
