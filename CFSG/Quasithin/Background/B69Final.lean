module

public import CFSG.Quasithin.Background.B69Main
public import CFSG.Quasithin.Vol2.Ch3yB69

public section

namespace CFSG.Quasithin

theorem b69One_of_inputs (h42 : AsB42) (hP4 : AsB15Part4) (hA21 : AsA21SQTKSection)
    (hex : B69.AsB69StrongExcluded) : B69One := by
  intro V _ _ hV X S M hH hmp hO2
  exact B69.not_isStrongFFModule_of_inputs h42 hP4 hA21 hex hV S M hH hmp hO2

end CFSG.Quasithin
