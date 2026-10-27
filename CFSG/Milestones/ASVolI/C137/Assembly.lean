module

public import CFSG.Milestones.ASVolI.C137.U33
public import CFSG.Milestones.ASVolI.C137.SMain
public import CFSG.Milestones.ASVolI.C137.A6Case
public import CFSG.Milestones.ASVolI.C137.L32Nat

public section

namespace CFSG.ASVolI


theorem burnsideC137_C_1_37_of_hat
    (hH : burnsideC137_CaseHat) : C_1_37 :=
  burnsideC137_C_1_37_of_corr (burnsideC137_corr_of_cases burnsideC137_caseU33
    burnsideC137_caseL32Nat burnsideC137_caseL32Sum burnsideC137_caseA6 hH)

end CFSG.ASVolI
