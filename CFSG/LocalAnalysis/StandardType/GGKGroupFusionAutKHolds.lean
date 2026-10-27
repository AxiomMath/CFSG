module

public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionAutKThree
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionAutKOrth

public section

namespace CFSG.StandardType


theorem ggLieOutRankTwoRestInput_holds : GGLieOutRankTwoRestInput := by
  rintro ⟨d, hv⟩ hd
  cases d with
  | A r q =>
    obtain ⟨rfl, -⟩ := hd
    exact ggLieOutRankTwoAt_A_one q hv
  | B r q => exact ggLieOutRankTwoAt_B_three r q hv hd.1 hd.2
  | D r q => exact ggLieOutRankTwoAt_D_three r q hv hd
  | twistedD r q => exact ggLieOutRankTwoAt_twistedD_three r q hv hd
  | E6 q => exact ggLieOutRankTwoAt_E6_three q hv hd
  | twistedE6 q => exact ggLieOutRankTwoAt_twistedE6_three q hv hd
  | _ => exact hd.elim


theorem ggLieOutRankTwoInput_holds : GGLieOutRankTwoInput :=
  ggLieOutRankTwoInput_of_rest ggLieOutRankTwoRestInput_holds

end CFSG.StandardType
