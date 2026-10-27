module

public import CFSG.Quasithin.Vol2.Ch8InputsProved
public import CFSG.Quasithin.Vol2.Ch8Sec3Lem832
public import CFSG.Quasithin.Vol2.Ch8Sec3Lem835

public section

namespace CFSG.Quasithin.H13

theorem stmt8_3_1_of_8310_8314
    (h63 : ASInputs.AS_E_6_3) (h8310 : Stmt8_3_10) (h8314 : Stmt8_3_14) : Stmt8_3_1 :=
  stmt8_3_1_of_steps (stmt8_3_2_of h63)
    (stmt8_3_5_of (stmtFSUModule_of_eight stmt3_2_2_eight_proved) input7_0_2_unique_proved
      input8_3_Q_proved (stmt8_3_2_of h63))
    h8310 h8314

end CFSG.Quasithin.H13
