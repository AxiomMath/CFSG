module

public import CFSG.Milestones.ASVolI.F429.Even
public import CFSG.Milestones.ASVolI.F429.aC2U4Full
public import CFSG.Milestones.ASVolI.F429.aC2U5Full

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin

theorem burnsideF429_EvenU2c_proof : burnsideF429_EvenU2c := by
  intro κ f E _ Gp M₁ M₂ hyp hU _ T hT
  rcases hU with rfl | rfl
  · exact burnsideF429a_c2c_U4 hyp hT
  · exact burnsideF429a_c2c_U5 hyp hT

section Corr

theorem burnsideF429_as_F_4_29_corr : burnsideF429_F_4_29_corr :=
  burnsideF429_corr_of_U2c burnsideF429_EvenU2c_proof

end Corr

end CFSG.ASVolI
