module

public import CFSG.Milestones.ASVolI.F431.ASp2Facts
public import CFSG.Milestones.ASVolI.F431.BCoreSpAll

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF

section F439Final

set_option linter.unusedSectionVars false


theorem burnsideF4m_F_4_39 : F_4_39 :=
  burnsideF4m_F_4_39_of' burnsideF4m_lieCoreSp burnsideF4m_sp2Facts burnsideF4m_topSp2

end F439Final

end CFSG.ASVolI
