module

public import CFSG.Quasithin.Background.F918V6
public import CFSG.Quasithin.Background.F918WC

public section

namespace CFSG.Quasithin

theorem d35InspUniq8_of_chk (h : CFSG.Quasithin.D35ValChk.run = true) : D35InspUniq8 :=
  d35InspUniq8_of_core (d35ValCore_of_chk h)

end CFSG.Quasithin
