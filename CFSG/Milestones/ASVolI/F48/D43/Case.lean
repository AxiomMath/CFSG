module

public import CFSG.Milestones.ASVolI.F48.D43.Dispatch
public import CFSG.Milestones.ASVolI.F48.Assembly

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF

section Case


theorem burnsideF48d_D43Case : burnsideF48_D43Case :=
  fun _ _ _ _ _ hyp => burnsideF48d_small_D4tw_three as_F_4_5 as_F_4_6 hyp

end Case

section Asm


theorem burnsideF48d_F_4_8 : F_4_8 := burnsideF48_F_4_8_of_D43 burnsideF48d_D43Case

theorem burnsideF48d_F_4_17 : F_4_17 := burnsideF48_F_4_17_of_D43 burnsideF48d_D43Case

end Asm

end CFSG.ASVolI
