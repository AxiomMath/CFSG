module

public import CFSG.Milestones.ASVolI.C31.J4KWP0
public import CFSG.Milestones.ASVolI.C31.Core

public section

namespace CFSG.ASVolI

theorem burnsideJ4KW_as_C_3_1_of_maxNonParabolicP0
    (h : burnsideJ4KW_MaxNonParabolicP0) : C_3_1 :=
  burnsideC31_as_C_3_1_of_core (burnsideJ4KW_core_of_maxNonParabolicP0 h)

end CFSG.ASVolI
