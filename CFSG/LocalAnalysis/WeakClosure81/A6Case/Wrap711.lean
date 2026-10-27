module

public import CFSG.LocalAnalysis.WeakClosure81.A6Case.Main
public import CFSG.LocalAnalysis.WeakClosure81.SzExcl.Wrap711

public section

namespace CFSG.LocalAnalysis.WeakClosure81.A6Case

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (W3Lem711 W3Thm88)

variable {G : Type} [Group G] [Finite G] {V H E : Subgroup G}

theorem w3Lem711Alt_of_inputs (hTim : TimmesfeldTIRootInput) (hGen : TwoConjugateGeneration)
    (hCore : OddTranspositionCoreInputSC) (hList : OddTranspListBundle)
    (hIn : OrthReflParabolic) : W3Lem711Alt G :=
  CFSG.LocalAnalysis.WeakClosure81.SzExcl.w3Lem711Alt_of_inputs hTim hGen
    (sevenElevenASixInput_holds G) hCore hList hIn

theorem w3Lem711Alt_subgroups_of_inputs (hTim : TimmesfeldTIRootInput)
    (hGen : TwoConjugateGeneration)
    (hCore : OddTranspositionCoreInputSC) (hList : OddTranspListBundle)
    (hIn : OrthReflParabolic) : ∀ H : Subgroup G, W3Lem711Alt ↥H :=
  CFSG.LocalAnalysis.WeakClosure81.SzExcl.w3Lem711Alt_subgroups_of_inputs hTim hGen
    (fun K _ _ => sevenElevenASixInput_holds K) hCore hList hIn

end CFSG.LocalAnalysis.WeakClosure81.A6Case

end
