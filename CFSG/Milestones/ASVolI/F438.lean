module

public import CFSG.Milestones.ASVolI.F442.Final
public import CFSG.Milestones.ASVolI.F431.RonanOddU5Main
public import CFSG.Milestones.ASVolI.F431.Final4

public section

namespace CFSG.ASVolI

section F438

set_option linter.unusedSectionVars false


theorem as_F_4_38 : F_4_38 :=
  burnsideF4m_F_4_38_of_U2 oddIndexU2

theorem as_F_4_40 : F_4_40 :=
  burnsideF4m_F_4_40_final4 oddIndexU2 burnsideF4r_A35Rest4

theorem as_F_4_42 : F_4_42 :=
  burnsideF4m_F_4_42_final4 oddIndexU2 (burnsideF4r_A42Rest'''_of4 burnsideF42g_A42Rest4)

theorem as_F_4_43 : F_4_43 :=
  burnsideF4m_F_4_43_final5 oddIndexU2 burnsideF4r_A35Rest4
    (burnsideF4r_A42Rest'''_of4 burnsideF42g_A42Rest4)

end F438

end CFSG.ASVolI
