module

public import CFSG.Milestones.ASVolI.A3L3Fact
public import CFSG.Milestones.ASVolI.A3Aut.A315
public import CFSG.Milestones.ASVolI.A3Spor.Main

public section

namespace CFSG.ASVolI

section Certificates


theorem as_A_3_15
    : A_3_15 :=
  burnsideA315y_A_3_15_of CFSG.Quasithin.a23SQTKListFact burnsideAut_a315LieConcrete
    burnsideA315s_sporadicFact

end Certificates

end CFSG.ASVolI
