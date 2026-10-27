module

public import CFSG.Milestones.ASVolI.C135.WMain
public import CFSG.Milestones.ASVolI.C135.Final

public section

namespace CFSG.ASVolI

section C135

set_option linter.unusedSectionVars false


theorem as_C_1_35
    : C_1_35 :=
  burnsideC135_C_1_35_ofW CFSG.Quasithin.MS93.burnsideC134w_c134W_holds

theorem as_C_1_36
    : C_1_36 :=
  burnsideC135_C_1_36_ofW CFSG.Quasithin.MS93.burnsideC134w_c134W_holds

end C135

end CFSG.ASVolI
