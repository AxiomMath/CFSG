module

public import CFSG.Milestones.ASVolI.F431.L39
public import CFSG.Milestones.ASVolI.F431.BCoreSpB
public import CFSG.Milestones.ASVolI.F431.BCoreSpOdd

public section

namespace CFSG.ASVolI

open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Open

theorem burnsideF4m_lieCoreSp : burnsideF4m_LieCoreSp := by
  intro f E _ Gp M₁ M₂ hyp hf
  haveI := hyp.finite
  by_cases hodd : Odd Gp.index
  · exact burnsideF4m_sp4_core_odd hyp hf hodd
  · exact burnsideF4m_sp4_core hyp hf hodd

end CFSG.ASVolI
