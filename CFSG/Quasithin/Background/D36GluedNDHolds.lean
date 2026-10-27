module

public import CFSG.Quasithin.Background.D36GluedNDInnerW

public section

namespace CFSG.Quasithin

theorem d36GluedNonDiag_of_L24
    (hL38 : D3L38) (hres : NDResidualL24) : D36GluedNonDiag :=
  d36GluedNonDiag_of_residual hL38 d36Inner_holds hres

theorem d36ActsGlued_of_L24
    (hL38 : D3L38) (hres : NDResidualL24) : D36ActsGlued :=
  d36ActsGlued_of_nondiag hL38 (d36GluedNonDiag_of_L24 hL38 hres)

end CFSG.Quasithin
