module

public import CFSG.Milestones.ASVolI.C31.J4NP.Final
public import CFSG.Milestones.ASVolI.C31.J4NP.Star

public section

namespace CFSG.ASVolI

section P0

set_option linter.unusedSectionVars false

theorem burnsideJ4KW_maxNonParabolicP0_holds : burnsideJ4KW_MaxNonParabolicP0 :=
  burnsideJ4NP_maxNonParabolicP0_of_openReachP burnsideJ4NP_openReachP

end P0

section KW

set_option linter.unusedSectionVars false

theorem burnsideJ4KW_twoLocals_holds : CFSG.Quasithin.KGJ4.J4TwoLocalsKW :=
  burnsideJ4KW_twoLocals_of_maxNonParabolic
    (burnsideJ4KW_maxNonParabolic_of_core
      (burnsideJ4KW_maxNonParabolicCore_of_P0 burnsideJ4KW_maxNonParabolicP0_holds))

end KW

end CFSG.ASVolI
