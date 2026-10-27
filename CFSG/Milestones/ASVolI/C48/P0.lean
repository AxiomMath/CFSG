module

public import CFSG.Milestones.ASVolI.C48.BigYS
public import CFSG.Quasithin.MS93.Burnside.C134BigProof
public import CFSG.Quasithin.MS93.Burnside.Mag568Main

public section

namespace CFSG.ASVolI

section C48P0

set_option linter.unusedSectionVars false


theorem burnsideC48w_C_4_8_of_P0
    (hP0 : burnsideJ4KW_MaxNonParabolicP0) : C_4_8 :=
  burnsideC48w_C_4_8_of_big_P0
    (CFSG.Quasithin.MS93.burnsideC134w_corrBig CFSG.Quasithin.MS93.S4L.burnsideMag568_noNonlinSLGt4)
    hP0

end C48P0

end CFSG.ASVolI
