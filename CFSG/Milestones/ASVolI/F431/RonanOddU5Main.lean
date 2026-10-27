module

public import CFSG.Milestones.ASVolI.F431.RonanOddU4Main
public import CFSG.Milestones.ASVolI.F431.RonanOddU5

public section

namespace CFSG.ASVolI

section Main

set_option linter.unusedSectionVars false



theorem oddIndexU2 : burnsideF4m_OddIndexU2 := by
  intro κ f E _ Gp M₁ M₂ Y _ β M _ ε z hyp hL43 hκ
  rcases hκ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact oddIndex_U4 E Gp M₁ M₂ Y β M ε z hyp hL43
  · exact oddIndex_U5 E Gp M₁ M₂ Y β M ε z hyp hL43

end Main

end CFSG.ASVolI
