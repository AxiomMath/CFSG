module

public import CFSG.LocalAnalysis.StandardType.GGSixLieKnownPosExcNoF4NoPSUPSpDefs
public import CFSG.LocalAnalysis.StandardType.GGSixLieKnownPosExcNoF4Defs
import CFSG.LocalAnalysis.StandardType.GGLieKnownR2PSpPos
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.NbrPSU
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.NbrPSp

public section

namespace CFSG.StandardType.LieKnownR2

theorem ggSixLieKnownRemainingPosExcNoF4_of_noPSUPSp
    (h : GGSixLieKnownRemainingPosExcNoF4NoPSUPSp) : GGSixLieKnownRemainingPosExcNoF4 := by
  obtain ⟨hOp, hOm, hE6, hE7, hE8, hT⟩ := h
  exact ⟨PSU.ggSixLieKnown_PSU_of_explicit fun _ _ _ => ClassicalPosition.ggSixPSUPosExplicit_holds,
    PSp.ggSixLieKnown_PSp_of_explicit fun _ _ _ => ClassicalPosition.ggSixPSpPosExplicit_holds, hOp,
    hOm, hE6, hE7, hE8, hT⟩

end CFSG.StandardType.LieKnownR2
