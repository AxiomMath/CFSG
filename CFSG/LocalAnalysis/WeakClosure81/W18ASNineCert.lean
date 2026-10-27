module

public import CFSG.LocalAnalysis.WeakClosure81.W18ASNineFam
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.ComponentClassification.CatLeafProof (lieOrderFormulasInput)

section Reduction

variable {G : Type} [Group G] [Finite G]


theorem tail189Two_AS_of_sevenElevenInputs (hCore : OddTranspositionCoreInputSC)
    (hList : OddTranspListBundle)
    (h772 : ∀ (X : Type) [Group X] [Finite X], SevenSevenTwoInput X)
    (hIn : OrthReflParabolic) : Tail189Two_AS G :=
  tail189Two_AS_of_lieOrderFormulas lieOrderFormulasInput hCore hList h772 hIn

end Reduction

end CFSG.LocalAnalysis.WeakClosure81

end
