module

public import CFSG.Quasithin.Background.D36GluedA5Final
public import CFSG.Quasithin.Background.D36GluedNDHolds

public section

namespace CFSG.Quasithin

theorem d36ActsGlued_of_L38
    (hL38 : D3L38) :
    D36ActsGlued :=
  d36ActsGlued_of_L24 hL38 ndResidualL24_holds

end CFSG.Quasithin
