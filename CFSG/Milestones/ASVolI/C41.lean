module

public import CFSG.Milestones.ASVolI.C41.BigYS
public import CFSG.Quasithin.MS93.Burnside.C134BigProof
public import CFSG.Quasithin.MS93.Burnside.Mag568Main

public section

namespace CFSG.ASVolI

section C41

set_option linter.unusedSectionVars false


theorem as_C_4_1
    : C_4_1 :=
  burnsideC41w_C_4_1_of_big
    (CFSG.Quasithin.MS93.burnsideC134w_corrBig CFSG.Quasithin.MS93.S4L.burnsideMag568_noNonlinSLGt4)

theorem as_C_4_7
    : C_4_7 :=
  burnsideC41w_C_4_7_of_big
    (CFSG.Quasithin.MS93.burnsideC134w_corrBig CFSG.Quasithin.MS93.S4L.burnsideMag568_noNonlinSLGt4)

end C41

end CFSG.ASVolI
