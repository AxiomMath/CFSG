module

public import CFSG.LocalAnalysis.WeakClosure81.SzExcl.Main
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveTwoSplit

public section

namespace CFSG.LocalAnalysis.WeakClosure81.SzExcl

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (W3Lem711 W3Thm88)

variable {G : Type} [Group G] [Finite G] {V H E : Subgroup G}

theorem w3Lem711Alt_of_inputs (hTim : TimmesfeldTIRootInput) (hGen : TwoConjugateGeneration)
    (hA6 : SevenElevenASixInput G) (hCore : OddTranspositionCoreInputSC)
    (hList : OddTranspListBundle)
    (hIn : OrthReflParabolic) : W3Lem711Alt G :=
  CFSG.LocalAnalysis.WeakClosure81.w3Lem711Alt_of_inputs hTim hGen hA6 hCore hList
    (CFSG.LocalAnalysis.WeakClosure81.SzExcl.sevenSevenTwoInput_holds G) hIn

theorem w3Lem711Alt_subgroups_of_inputs (hTim : TimmesfeldTIRootInput)
    (hGen : TwoConjugateGeneration)
    (hA6 : ∀ (K : Type) [Group K] [Finite K], SevenElevenASixInput K)
    (hCore : OddTranspositionCoreInputSC) (hList : OddTranspListBundle)
    (hIn : OrthReflParabolic) : ∀ H : Subgroup G, W3Lem711Alt ↥H :=
  CFSG.LocalAnalysis.WeakClosure81.w3Lem711Alt_subgroups_of_inputs hTim hGen hA6 hCore hList
    CFSG.LocalAnalysis.WeakClosure81.SzExcl.sevenSevenTwoInput_forall hIn

end CFSG.LocalAnalysis.WeakClosure81.SzExcl
