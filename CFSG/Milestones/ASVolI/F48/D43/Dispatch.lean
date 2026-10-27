module

public import CFSG.Milestones.ASVolI.F48.D43.Main
public import CFSG.Milestones.ASVolI.F48.D43.EMain

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF


theorem burnsideF48d_small_D4tw_three (h45 : F_4_5) (h46 : F_4_6) {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : HypF_4_4 .D4tw 3 1 Gp M₁ M₂) : F48Concl .D4tw 3 1 Gp M₁ M₂ := by
  by_cases hGp : Gp = ⊤
  · exact burnsideF48d_small_D4tw_three_top h45 h46 hyp hGp
  · exact burnsideF48dE_extCase burnsideF48d_modelFacts E Gp M₁ M₂ hyp hGp

end CFSG.ASVolI
