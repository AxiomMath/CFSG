module

public import CFSG.LocalAnalysis.WeakClosure81.SevenEleven
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveTwoSplitDefs
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenW3

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (W3Lem711 W3Thm88)

variable {G : Type} [Group G] [Finite G]

theorem w3Lem711Alt_of_inputs (hTim : TimmesfeldTIRootInput) (hGen : TwoConjugateGeneration)
    (hA6 : SevenElevenASixInput G) (hCore : OddTranspositionCoreInputSC)
    (hList : OddTranspListBundle)
    (h772 : SevenSevenTwoInput G)
    (hIn : OrthReflParabolic) : W3Lem711Alt G := by
  intro V H E h
  refine ⟨(seven_eleven hTim hGen hA6 hCore hList h772 hIn h (isBarMap_mk_pCore _)).1, ?_⟩
  intro X _ φ hφ
  exact (seven_eleven hTim hGen hA6 hCore hList h772 hIn h hφ).2

theorem w3Lem711Alt_subgroups_of_inputs (hTim : TimmesfeldTIRootInput)
    (hGen : TwoConjugateGeneration)
    (hA6 : ∀ (K : Type) [Group K] [Finite K], SevenElevenASixInput K)
    (hCore : OddTranspositionCoreInputSC) (hList : OddTranspListBundle)
    (h772 : ∀ (K : Type) [Group K] [Finite K], SevenSevenTwoInput K)
    (hIn : OrthReflParabolic) : ∀ H : Subgroup G, W3Lem711Alt ↥H :=
  fun H => w3Lem711Alt_of_inputs hTim hGen (hA6 ↥H) hCore hList (h772 ↥H) hIn

end CFSG.LocalAnalysis.WeakClosure81

end
