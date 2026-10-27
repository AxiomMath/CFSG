module

public import CFSG.Milestones.ASVolI.F437.Odd
public import CFSG.Milestones.ASVolI.F431.BCoreTop

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF

section Top

set_option linter.unusedSectionVars false

theorem burnsideF437_F_4_37_of_U (hU4 : burnsideF437_F437KindDeg .U4 1)
    (hU5 : burnsideF437_F437KindDeg .U5 1) : F_4_37 :=
  burnsideF437_F_4_37_of_lie burnsideF4m_lieCoreInput hU4 hU5

end Top

end CFSG.ASVolI
