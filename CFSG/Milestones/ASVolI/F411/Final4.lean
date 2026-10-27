module

public import CFSG.Milestones.ASVolI.F411.Final3
public import CFSG.Milestones.ASVolI.F411.aSwL3

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF

@[expose] def burnsideF411_L3OneSwapInput : Prop :=
  ∀ (p f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    HypF_4_4 .L3 p f Gp M₁ M₂ → Gp ≠ ⊤ → p % 3 = 1 → burnsideF411_Swap M₁ M₂

theorem burnsideF411_swapInputKind_L3_of (h : burnsideF411_L3OneSwapInput) :
    burnsideF411_SwapInputKind .L3 := by
  intro p f E _ Gp M₁ M₂ hyp hGp
  by_cases hp : p % 3 = 1
  · exact h p f E Gp M₁ M₂ hyp hGp hp
  · exact burnsideF411a_swap_L3_of_mod hyp hp

theorem burnsideF411_rigidExt_of_L3One
    (h : burnsideF411_L3OneSwapInput) : burnsideF4n_F411RigidExt :=
  burnsideF411_rigidExt_of_swapL3 (burnsideF411_swapInputKind_L3_of h)

end CFSG.ASVolI
