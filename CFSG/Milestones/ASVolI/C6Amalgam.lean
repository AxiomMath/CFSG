module

public import CFSG.Milestones.ASVolI.C61.Glue4
public import CFSG.Milestones.ASVolI.C61.A3Six
public import CFSG.Milestones.ASVolI.C61.Fin7

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC

section


theorem as_C_6_1
    : C_6_1 :=
  burnsideC56_C61_of_fin (burnsideC56_C61_fin_of fun hcs h3 hj =>
    burnsideC56_P.burnsideC56_a3_six hcs h3 hj)

end

end CFSG.ASVolI
