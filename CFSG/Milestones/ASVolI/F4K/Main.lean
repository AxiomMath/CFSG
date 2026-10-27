module

public import CFSG.Milestones.ASVolI.F4K.F415
public import CFSG.Milestones.ASVolI.F4K.Poly
public import CFSG.Milestones.ASVolI.F4K.Grp
public import CFSG.Milestones.ASVolI.F4K.G2d
public import CFSG.Milestones.ASVolI.F4Native

public section

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF

theorem burnsideF4k_facts46All
    (h46 : F_4_6) : burnsideF4b_Facts46All :=
  burnsideF4b_Facts46All_of_F46 h46 (burnsideF4b_parabolics_of_compat ChF.nativeChartCompatibility)

theorem burnside_as_F_4_12_of
    (_h45 : F_4_5) (h46 : F_4_6) : F_4_12 :=
  burnsideF4b_F412 (burnsideF4k_facts46All h46)

theorem burnside_as_F_4_13_of
    (h45 : F_4_5) (h46 : F_4_6) : F_4_13 :=
  burnsideF4b_F413 (burnsideF4k_facts46All h46)
    (burnsideF4b_IotaSmall_of (burnsideF4k_facts46All h46) h45)

theorem burnside_as_F_4_14_of
    (_h45 : F_4_5) (h46 : F_4_6) : F_4_14 :=
  burnsideF4b_F414 (burnsideF4k_facts46All h46)

theorem burnside_as_F_4_16_of
    (h45 : F_4_5) (h46 : F_4_6) : F_4_16 :=
  burnsideF4k_F416_of_F45 h46 h45 ChF.nativeChartCompatibility

theorem burnside_as_F_4_15_of
    (h45 : F_4_5) (h46 : F_4_6) : F_4_15 :=
  burnsideF4k_F415_of burnsideF4k_polyArcs burnsideF4k_polyRefl burnsideF4k_polyW
    burnsideF4k_polyOpp burnsideF4k_polyNbr burnsideF4k_polyG2d burnsideF4k_grpD10
    burnsideF4k_grpZ3 burnsideF4k_grpTwoTrans h46 h45 ChF.nativeChartCompatibility

end CFSG.ASVolI
