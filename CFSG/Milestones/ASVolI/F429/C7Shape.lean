module

public import CFSG.Milestones.ASVolI.F429.Cl7
public import CFSG.Milestones.ASVolI.F429.aC7L3
public import CFSG.Milestones.ASVolI.F429.aC7Sp4
public import CFSG.Milestones.ASVolI.F429.aC7U4
public import CFSG.Milestones.ASVolI.F429.aC7U5

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin

theorem burnsideF429_c7ClassicalShape : burnsideF429_C7ClassicalShape := by
  intro κ f E _ Gp M₁ M₂ hyp hκ
  rcases hκ with rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inl ⟨rfl, burnsideF429a_c7_L3 hyp⟩)
  · exact Or.inr (Or.inr ⟨rfl, burnsideF429a_c7_Sp4 hyp⟩)
  · exact Or.inl (burnsideF429a_c7_U4 hyp)
  · exact Or.inl (burnsideF429a_c7_U5 hyp)

end CFSG.ASVolI
