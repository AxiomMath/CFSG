module

public import CFSG.Quasithin.Vol2.Ch12Sec2Thm
public import CFSG.Quasithin.Vol2.GoldschmidtTD32
public import CFSG.Quasithin.Vol2.GoldschmidtG2ZornModel

public section

namespace CFSG.Quasithin.H13

theorem stmt12_2_2_of_12111
    (h1001 : Stmt10_0_1) (h325 : Stmt3_2_5)
    (h6220 : Stmt6_2_20) (h701 : Stmt7_0_1) (h1101 : Stmt11_0_1) (h12111 : Stmt12_1_11) :
    Stmt12_2_2 :=
  stmt12_2_2_of_inputs h1001 stmt3_2_3_proved h325 stmt3_2_8_proved h6220 h701 h1101 h12111
    g2ZornQuotientModel_holds

end CFSG.Quasithin.H13
