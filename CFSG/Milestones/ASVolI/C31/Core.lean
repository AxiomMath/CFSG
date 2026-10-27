module

public import CFSG.Milestones.ASVolI.C31.Asm
public import CFSG.Milestones.ASVolI.C31.KW

public section

namespace CFSG.ASVolI

theorem burnsideC31_as_C_3_1_of_core
    (hcore : burnsideC31_J4KWCore) : C_3_1 :=
  burnsideC31_as_C_3_1_of_KW (burnsideC31_kw_of_core hcore)

end CFSG.ASVolI
