module

public import CFSG.Milestones.ASVolI.F431.BCoreTop
public import CFSG.Milestones.ASVolI.F431.Asm2

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

section Done

set_option linter.unusedSectionVars false

theorem burnsideF4m_F_4_38_of_U2 (hU : burnsideF4m_OddIndexU2) : F_4_38 :=
  burnsideF4m_F_4_38_of_core burnsideF4m_lieCoreInput hU

theorem burnsideF4m_F_4_35_of_rest' (hrest : burnsideF4m_F435Rest) : F_4_35 :=
  burnsideF4m_F_4_35_of burnsideF4m_lieCoreSp hrest

end Done

end CFSG.ASVolI
