module

public import CFSG.Milestones.ASVolI.F411.Final4
public import CFSG.Milestones.ASVolI.F411.L3Key
public import CFSG.Milestones.ASVolI.F411.aSwL3BMain

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF

theorem burnsideF411_l3OneSwapInput : burnsideF411_L3OneSwapInput := by
  intro p f E _ Gp M₁ M₂ hyp _ hp
  have hp3 : p ≠ 3 := by
    rintro rfl
    norm_num at hp
  obtain ⟨hR1, hR2⟩ := burnsideF411_l3_pCoreOf_eq hyp hp3
  exact burnsideF411a_swap_L3_one hyp hp hR1 hR2

theorem burnsideF411_F411RigidExt :
    burnsideF4n_F411RigidExt :=
  burnsideF411_rigidExt_of_L3One burnsideF411_l3OneSwapInput

end CFSG.ASVolI
