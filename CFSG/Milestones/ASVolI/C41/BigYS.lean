module

public import CFSG.Milestones.ASVolI.C41.BigStmt
public import CFSG.Milestones.ASVolI.C27
public import CFSG.Milestones.ASVolI.C41.MS93RUse

public section

namespace CFSG.ASVolI

section C41Big

set_option linter.unusedSectionVars false


theorem burnsideC41w_C_4_1_of_big
    (hb : CFSG.Quasithin.MS93.burnsideC134w_AS_C_1_34_corrBig) :
    C_4_1 :=
  burnsideC4h_c41_of_wip
    (fun G _ _ => CFSG.Quasithin.C41Pf.burnsideC41w_asc41Statement_of_big (as_C_2_7 G) hb)
    burnsideMS93R_clauseBridge

theorem burnsideC41w_C_4_7_of_big
    (hb : CFSG.Quasithin.MS93.burnsideC134w_AS_C_1_34_corrBig) :
    C_4_7 :=
  burnsideC4h_c47_of_wip
    (fun G _ _ => CFSG.Quasithin.C41Pf.burnsideC41w_asc41Statement_of_big (as_C_2_7 G) hb)
    burnsideMS93R_clauseBridge

end C41Big

end CFSG.ASVolI
