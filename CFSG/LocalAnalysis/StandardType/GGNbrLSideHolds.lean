module

public import CFSG.LocalAnalysis.StandardType.GGNbrLSideGlue
public import CFSG.LocalAnalysis.StandardType.GGNbrLSide35

public section

namespace CFSG.StandardType

theorem ggNbrLSide_of_rs
    (hRS : GGNbrLSideRS) : GGNbrLSide :=
  ggNbrLSide_of_rs_35 hRS ggNbrLSide35_holds

end CFSG.StandardType

end
