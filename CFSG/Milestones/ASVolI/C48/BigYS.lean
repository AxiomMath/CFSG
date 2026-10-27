module

public import CFSG.Milestones.ASVolI.C48.Main
public import CFSG.Milestones.ASVolI.C31.J4KWC31
public import CFSG.Milestones.ASVolI.C41.BigYS

public section

namespace CFSG.ASVolI

section C48Big

set_option linter.unusedSectionVars false

theorem burnsideC48w_C_4_8_of_big_P0
    (hb : CFSG.Quasithin.MS93.burnsideC134w_AS_C_1_34_corrBig)
    (hP0 : burnsideJ4KW_MaxNonParabolicP0) : C_4_8 :=
  burnsideC48_C_4_8_of_KW (burnsideJ4KW_as_C_3_1_of_maxNonParabolicP0 hP0)
    (burnsideC41w_C_4_1_of_big hb)
    (burnsideJ4KW_twoLocals_of_maxNonParabolic
      (burnsideJ4KW_maxNonParabolic_of_core (burnsideJ4KW_maxNonParabolicCore_of_P0 hP0)))

end C48Big

end CFSG.ASVolI
