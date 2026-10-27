module

public import CFSG.Milestones.ASVolI.F48.Rest.U52eMain
public import CFSG.Milestones.ASVolI.F4Lie

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF

@[expose] def burnsideF48_D43Case : Prop :=
  ∀ (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E), HypF_4_4 .D4tw 3 1 Gp M₁ M₂ →
    F48Concl .D4tw 3 1 Gp M₁ M₂

section Asm

set_option linter.unusedSectionVars false


theorem burnsideF48_F_4_8_of_D43 (hD : burnsideF48_D43Case) : F_4_8 :=
  burnsideF48s_F_4_8_of_rest as_F_4_5 as_F_4_6 (burnsideF48t_smallRest_of_D43 as_F_4_5 as_F_4_6 hD)

theorem burnsideF48_F_4_17_of_D43 (hD : burnsideF48_D43Case) : F_4_17 :=
  burnsideF4b_F417 (burnsideF48_F_4_8_of_D43 hD)

end Asm

end CFSG.ASVolI
