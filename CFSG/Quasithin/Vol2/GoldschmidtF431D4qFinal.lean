module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qMain
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qStd

public section

namespace CFSG.Quasithin.H13.F431.D4q

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint

set_option linter.unusedSectionVars false


theorem f431Rank2At_d4q : F431Rank2At .trialityD4 0 :=
  f431Rank2At_of_std fun f hf => Local.std3D4_holds f hf

end CFSG.Quasithin.H13.F431.D4q
