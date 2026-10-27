module

public import CFSG.LocalAnalysis.StandardType.GGExcElemToralF4
public import CFSG.LocalAnalysis.StandardType.GGExcElemToralE8
public import CFSG.LocalAnalysis.StandardType.GGExcElemToralE7
public import CFSG.LocalAnalysis.StandardType.GGExcElemToralE6

public section

namespace CFSG.StandardType


theorem ggExcElemToralRest_holds : GGExcElemToralRest :=
  ⟨ggExcElemToralRestInput_F4, ggE6ElemToralFiveInput_holds, ggExcElemToralRestInput_E7,
    ggExcElemToralRestInput_E8⟩

end CFSG.StandardType
