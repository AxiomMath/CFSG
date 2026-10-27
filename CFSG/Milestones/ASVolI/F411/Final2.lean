module

public import CFSG.Milestones.ASVolI.F411.Final
public import CFSG.Milestones.ASVolI.F411.SpOdd
public import CFSG.Milestones.ASVolI.F411.aSwSp4
public import CFSG.Milestones.ASVolI.F411.aSwG2

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF

theorem burnsideF411_swapInputKind_Sp4 : burnsideF411_SwapInputKind .Sp4 := by
  intro p f E _ Gp M₁ M₂ hyp _
  by_cases hp : p = 2
  · subst hp
    exact burnsideF411a_swap_Sp4_two hyp
  · exact burnsideF411_swap_Sp4_odd hyp hp

@[expose] def burnsideF411_G2SwapInput : Prop :=
  ∀ (p f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    HypF_4_4 .G2 p f Gp M₁ M₂ → Gp ≠ ⊤ → p ≠ 3 → burnsideF411_Swap M₁ M₂

section Certs

theorem burnsideF411_swapInputKind_G2_of (hG2 : burnsideF411_G2SwapInput) :
    burnsideF411_SwapInputKind .G2 := by
  intro p f E _ Gp M₁ M₂ hyp hGp
  by_cases hp : p = 3
  · subst hp
    exact burnsideF411a_swap_G2_three hyp
  · exact hG2 p f E Gp M₁ M₂ hyp hGp hp

end Certs

end CFSG.ASVolI
