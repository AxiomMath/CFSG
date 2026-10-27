module

public import CFSG.Milestones.ASVolI.C31.J4NP.Final
public import CFSG.Milestones.ASVolI.C31.J4NP.Star
public import CFSG.Milestones.ASVolI.C31.J4KWC31

public section

namespace CFSG.ASVolI

section C31

set_option linter.unusedSectionVars false


theorem as_C_3_1
    : C_3_1 :=
  burnsideJ4KW_as_C_3_1_of_maxNonParabolicP0
    (burnsideJ4NP_maxNonParabolicP0_of_openReachP burnsideJ4NP_openReachP)

end C31

end CFSG.ASVolI
