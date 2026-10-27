module

public import CFSG.LocalAnalysis.StandardType.GGSixLieKnownPosExcDefs
public import CFSG.LocalAnalysis.StandardType.GGSixLieKnownPosNoPSLDefs
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2E6PosGlue
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2E7PosGlue
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2E8PosGlue

public section

namespace CFSG.StandardType.LieKnownR2

theorem ggSixLieKnownRemainingPosNoPSL_of_exc
    (h : GGSixLieKnownRemainingPosExc) : GGSixLieKnownRemainingPosNoPSL := by
  obtain ⟨hU, hSp, hOp, hOm, hF4, hE6, hE7, hE8, hT⟩ := h
  exact ⟨hU, hSp, hOp, hOm, F4.ggSixLieKnownPos_F4_of_explicit hF4,
    E6.ggSixLieKnown_of_pos_E6 hE6, E7.ggSixLieKnown_of_pos_E7 hE7,
    E8.ggSixLieKnown_of_pos_E8 hE8, hT⟩

end CFSG.StandardType.LieKnownR2
