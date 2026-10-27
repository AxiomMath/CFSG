module

public import CFSG.Milestones.ASVolI.F431.FinalAll
public import CFSG.Milestones.ASVolI.F431.AU5Final

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF

section Final2

set_option linter.unusedSectionVars false


theorem burnsideF4m_F_4_35_final' (h35 : burnsideF4m_A35Rest') : F_4_35 :=
  burnsideF4m_F_4_35_final (burnsideF4m_A35Rest_of' h35)

theorem burnsideF4m_F_4_40_final' (hU : burnsideF4m_OddIndexU2) (h35 : burnsideF4m_A35Rest') :
    F_4_40 :=
  burnsideF4m_F_4_40_final hU (burnsideF4m_A35Rest_of' h35)

theorem burnsideF4m_F_4_42_final' (hU : burnsideF4m_OddIndexU2) (h42 : burnsideF4m_A42Rest') :
    F_4_42 :=
  burnsideF4m_F_4_42_final hU (burnsideF4m_A42Rest_of' h42)

theorem burnsideF4m_F_4_43_final' (hU : burnsideF4m_OddIndexU2) (h35 : burnsideF4m_A35Rest')
    (h42 : burnsideF4m_A42Rest') : F_4_43 :=
  burnsideF4m_F_4_43_final hU (burnsideF4m_A35Rest_of' h35) (burnsideF4m_A42Rest_of' h42)

end Final2

end CFSG.ASVolI
