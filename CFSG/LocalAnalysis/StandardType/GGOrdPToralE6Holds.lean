module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutInnerExcHardE6Holds
import CFSG.LocalAnalysis.StandardType.GGOrdPToralF4Holds

public section

namespace CFSG.StandardType

theorem ggOrdPToralE6RestHard_holds :
    GGOrdPToralE6RestHard :=
  ggOrdPToralE6RestHard_of_F4 ggOrdPToralF4RestHard_holds

end CFSG.StandardType
