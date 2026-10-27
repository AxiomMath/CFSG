module

public import CFSG.LocalAnalysis.StandardType.GGQTwoVACSmall
public import CFSG.LocalAnalysis.StandardType.GGQTwoVACUnitDvd
public import CFSG.LocalAnalysis.StandardType.GGQTwoVACTwE6HeartCenter

public section

namespace CFSG.StandardType

theorem ggQTwoVACCell_of_guards
    (hCav : GGQ2CavOfTBFull) (hON : GGQTwoGuardFailsOn GGQ2VACLabOrthNonFull)
    (hE6 : GGQTwoGuardFailsOn (fun p lab => GGLabQTwo p lab ∧ lab.tag = .E6)) :
    GGQTwoVACCell :=
  ggQTwoVACCell_of_families ggQTwoVACCellOn_lin (ggQTwoGuardFailsOn_symp_of_cav hCav)
    (ggQTwoGuardFailsOn_orth hCav hON) (ggQTwoGuardFailsOn_unit hCav)
    (ggQTwoGuardFailsOn_exc_of_e6 hCav hE6) ggQTwoGuardFailsOn_small

end CFSG.StandardType
