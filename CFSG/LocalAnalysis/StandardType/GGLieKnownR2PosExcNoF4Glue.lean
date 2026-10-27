module

public import CFSG.LocalAnalysis.StandardType.GGSixLieKnownPosExcNoF4Defs
public import CFSG.LocalAnalysis.StandardType.GGSixLieKnownPosExcDefs
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.FinalAssembly

public section

namespace CFSG.StandardType.LieKnownR2

theorem ggSixLieKnownRemainingPosExc_of_noF4
    (h : GGSixLieKnownRemainingPosExcNoF4) : GGSixLieKnownRemainingPosExc := by
  obtain ⟨hU, hSp, hOp, hOm, hE6, hE7, hE8, hT⟩ := h
  exact ⟨hU, hSp, hOp, hOm, CFSG.StandardType.F4ExplicitPos.FinalAssembly.f4PosExplicit, hE6,
    hE7, hE8, hT⟩

end CFSG.StandardType.LieKnownR2
