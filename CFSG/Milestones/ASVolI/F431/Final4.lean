module

public import CFSG.Milestones.ASVolI.F431.Final3
public import CFSG.Milestones.ASVolI.F431.A42F4Two

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF

section Final4

set_option linter.unusedSectionVars false


theorem burnsideF4m_A42Rest'_of''' (hrest : burnsideF4m_A42Rest''') : burnsideF4m_A42Rest' :=
  burnsideF4m_A42Rest'_of'' (burnsideF4m_A42Rest''_of''' hrest)

theorem burnsideF4m_F_4_42_final4 (hU : burnsideF4m_OddIndexU2) (h42 : burnsideF4m_A42Rest''') :
    F_4_42 :=
  burnsideF4m_F_4_42_final' hU (burnsideF4m_A42Rest'_of''' h42)

theorem burnsideF4m_F_4_43_final5 (hU : burnsideF4m_OddIndexU2) (h35 : burnsideF4m_A35Rest4)
    (h42 : burnsideF4m_A42Rest''') : F_4_43 :=
  burnsideF4m_F_4_43_final4 hU h35 (burnsideF4m_A42Rest'_of''' h42)

end Final4

end CFSG.ASVolI
