module

public import CFSG.Quasithin.Background.F918V3Asm
public import CFSG.Quasithin.Background.F918V3T3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

theorem d392_of_suzuki
    (hS : D392Suzuki) : D392 :=
  d392_assemble hS fun _ _ _ _ _ hM hK hn => d392_three_dvd_component hM hK hn

end CFSG.Quasithin
