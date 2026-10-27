module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4F48D3Main
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4YAmalgam

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin

section Final

variable
  {D' : Type} [Group D'] (hD' : IsLieOverTwo .trialityD4 0 1 D')

include hD' in
theorem d3F424_of_simple (hD : IsSimpleGroup D) : D3F424 :=
  d3F424 hD' (d4_hZH hD) (d4_hNN hD) hD

end Final

end CFSG.Quasithin.D4Hex
