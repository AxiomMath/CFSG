module

public import CFSG.LocalAnalysis.WeakClosure81.SzExcl.Main
public import CFSG.LocalAnalysis.WeakClosure81.W18ASNineCert

public section

namespace CFSG.LocalAnalysis.WeakClosure81.SzExcl

open CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)

variable {G : Type} [Group G] [Finite G]

section Certificates

theorem tail189Two_AS_of_sevenElevenInputs (hCore : OddTranspositionCoreInputSC)
    (hList : OddTranspListBundle)
    (hIn : OrthReflParabolic) : Tail189Two_AS G :=
  CFSG.LocalAnalysis.WeakClosure81.tail189Two_AS_of_sevenElevenInputs hCore hList
    CFSG.LocalAnalysis.WeakClosure81.SzExcl.sevenSevenTwoInput_forall hIn

end Certificates

end CFSG.LocalAnalysis.WeakClosure81.SzExcl
