module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2PSLPos
public import CFSG.LocalAnalysis.StandardType.GGSixLieKnownPosNoPSLDefs

public section

namespace CFSG.StandardType.LieKnownR2.PSL

theorem ggSixLieKnownRemainingPos_of_noPSL
    (h : GGSixLieKnownRemainingPosNoPSL) : GGSixLieKnownRemainingPos :=
  ⟨ggSixLieKnown_PSL, h⟩

end CFSG.StandardType.LieKnownR2.PSL
