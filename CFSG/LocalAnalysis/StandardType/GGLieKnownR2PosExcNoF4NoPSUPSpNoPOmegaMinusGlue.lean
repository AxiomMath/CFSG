module

public import CFSG.LocalAnalysis.StandardType.GGSixLieKnownPosExcNoF4NoPSUPSpNoPOmegaMinusDefs
public import CFSG.LocalAnalysis.StandardType.GGSixLieKnownPosExcNoF4NoPSUPSpDefs
import CFSG.LocalAnalysis.StandardType.GGLieKnownR2POmegaPos
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.NbrPOmegaMinusAssembly

public section

namespace CFSG.StandardType.LieKnownR2

theorem ggSixLieKnownRemainingPosExcNoF4NoPSUPSp_of_noPOmegaMinus
    (h : GGSixLieKnownRemainingPosExcNoF4NoPSUPSpNoPOmegaMinus) :
    GGSixLieKnownRemainingPosExcNoF4NoPSUPSp := by
  obtain ⟨hOp, hE6, hE7, hE8, hT⟩ := h
  exact ⟨hOp, POmega.ggSixLieKnown_POmegaMinus_of_explicit
    ClassicalPosition.ggSixPOmegaMinusPosExplicit_holds, hE6, hE7, hE8, hT⟩

end CFSG.StandardType.LieKnownR2
