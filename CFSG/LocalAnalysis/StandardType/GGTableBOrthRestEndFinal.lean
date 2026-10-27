module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestTailFinal
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestEndD4
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestEndRankMinus

public section

namespace CFSG.StandardType

section Holds

theorem ggBstarInputOn_orthRest_of_odd (ha₀ : GGLNoncyclicInput)
    (hO : GGOrthRestBstarOddInput) : GGBstarInputOn (GGTableBRest3 GGTableBOrthLabel) :=
  ggBstarInputOn_orthRest_of_split ha₀ ggOrthRestMinusRankInput_holds hO
    ggOrthRestBstarD4Input_holds

end Holds

end CFSG.StandardType
