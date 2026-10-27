module

public import CFSG.Quasithin.Background.Harris.KFact2d.StepOne
public import CFSG.Quasithin.Background.Harris.KFact2d.StepZero
public import CFSG.Quasithin.EmptyFaithful.SzOneV2d

public section

namespace CFSG.Quasithin.Background.Harris.KFact2d

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem kfact2dAtoms_of (hS : StarStmt) (hF1 : F1Stmt) (hF4 : F4Stmt) :
    CFSG.Quasithin.Gap6R2.KFact2dAtoms := by
  intro G _ _ T N K K0 V hmp _ hK0 hKK0 _ hc hV hVT hTV hat
  by_cases hJT : kerIn N K ≤ T
  · exact caseI hS hmp hK0 hKK0 hc hJT hV hVT hTV hat
  · exact stepZero hF1 hmp hK0 hKK0 hc hV hVT hTV
      (stepOne hF4 hmp hK0 hKK0 hc hJT hV hVT hTV hat)

end CFSG.Quasithin.Background.Harris.KFact2d
