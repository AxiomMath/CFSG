module

public import CFSG.LocalAnalysis.StandardType.GGSixLieKnownPosExcNoF4NoPSUPSpNoPOmegaDefs
public import CFSG.LocalAnalysis.StandardType.GGSixLieKnownPosExcNoF4NoPSUPSpNoPOmegaMinusDefs
import CFSG.LocalAnalysis.StandardType.GGLieKnownR2POmegaPos
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.NbrPOmegaPlus

public section

namespace CFSG.StandardType.LieKnownR2

theorem ggSixLieKnownRemainingPosExcNoF4NoPSUPSpNoPOmegaMinus_of_noPOmega
    (h : GGSixLieKnownRemainingPosExcNoF4NoPSUPSpNoPOmega) :
    GGSixLieKnownRemainingPosExcNoF4NoPSUPSpNoPOmegaMinus := by
  obtain ⟨hE6, hE7, hE8, hT⟩ := h
  exact ⟨POmega.ggSixLieKnown_POmegaPlus_of_explicit
    ClassicalPosition.ggSixPOmegaPlusPosExplicit_holds, hE6, hE7, hE8, hT⟩

end CFSG.StandardType.LieKnownR2
