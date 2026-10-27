module

public import CFSG.Milestones.ASVolI.F4N.CMain
public import CFSG.Milestones.ASVolI.F4N.B


public section

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF

theorem burnside_as_F_4_20_of
    (h45 : F_4_5) (h46 : F_4_6) : F_4_20 :=
  burnsideF4nC_F420_of_g2d h45 h46 (burnsideF4nB_F420_G2d' h45 h46 (burnside_as_F_4_19_of h45 h46))

end CFSG.ASVolI
