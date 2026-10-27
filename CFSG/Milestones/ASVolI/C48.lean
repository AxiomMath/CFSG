module

public import CFSG.Milestones.ASVolI.C31.J4NP.Final
public import CFSG.Milestones.ASVolI.C31.J4NP.Star
public import CFSG.Milestones.ASVolI.C48.P0

public section

namespace CFSG.ASVolI

section C48

set_option linter.unusedSectionVars false


theorem as_C_4_8
    : C_4_8 :=
  burnsideC48w_C_4_8_of_P0 (burnsideJ4NP_maxNonParabolicP0_of_openReachP burnsideJ4NP_openReachP)

end C48

end CFSG.ASVolI
