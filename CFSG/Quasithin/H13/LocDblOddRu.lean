module

import all CFSG.Blueprint.NativeSporadic
public import CFSG.Quasithin.H13.LocDblOvergroups
public import CFSG.Quasithin.H13.LocDblRuCheck

public section

namespace CFSG.Quasithin.H13.LocDbl

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.SmallF2
open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.Sporadic.Ru.Native (ruData)

theorem oddIndexBound_Ru_group :
    OddIndexBound ↥(J ruData) [245760, 344064] :=
  oddIndexBound_of_overgroups RuCert.ru_S_sylow RuCert.ru_over_dvd

end CFSG.Quasithin.H13.LocDbl
