module

public import CFSG.Milestones.ASVolI.F431.A42Final
public import CFSG.Milestones.ASVolI.F431.L39Final
public import CFSG.Milestones.ASVolI.F431.Done

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF

section FinalAll

set_option linter.unusedSectionVars false


theorem burnsideF4m_F_4_35_final (h35 : burnsideF4m_A35Rest) : F_4_35 :=
  burnsideF4m_F_4_35_of_rest' (burnsideF4m_F435Rest_of h35)

theorem burnsideF4m_F_4_40_final (hU : burnsideF4m_OddIndexU2) (h35 : burnsideF4m_A35Rest) :
    F_4_40 :=
  burnsideF4m_F_4_40_of (burnsideF4m_F_4_35_final h35) (burnsideF4m_F_4_38_of_U2 hU)

theorem burnsideF4m_F_4_42_final (hU : burnsideF4m_OddIndexU2) (h42 : burnsideF4m_A42Rest) :
    F_4_42 :=
  burnsideF4m_F_4_42_of_rest (burnsideF4m_F_4_38_of_U2 hU) h42

theorem burnsideF4m_F_4_43_final (hU : burnsideF4m_OddIndexU2) (h35 : burnsideF4m_A35Rest)
    (h42 : burnsideF4m_A42Rest) : F_4_43 :=
  burnsideF4m_F_4_43_of (burnsideF4m_F_4_35_final h35) (burnsideF4m_F_4_38_of_U2 hU)
    burnsideF4m_F_4_39 (burnsideF4m_F_4_42_final hU h42)

end FinalAll

end CFSG.ASVolI
