module

public import CFSG.Milestones.ASVolI.F411.Final2
public import CFSG.Milestones.ASVolI.F411.aSwG2N

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF

theorem burnsideF411_swapInputKind_G2 :
    burnsideF411_SwapInputKind .G2 :=
  burnsideF411_swapInputKind_G2_of fun _ _ _ _ _ _ _ hyp hGp hp3 =>
    burnsideF411a_swap_G2_ne_three hyp hp3 hGp

theorem burnsideF411_rigidExt_of_swapL3
    (hSL3 : burnsideF411_SwapInputKind .L3) : burnsideF4n_F411RigidExt :=
  burnsideF411_rigidExt_of_swap hSL3 burnsideF411_swapInputKind_Sp4 burnsideF411_swapInputKind_G2

end CFSG.ASVolI
