module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34QBound
public import CFSG.Quasithin.Vol2.Ch5Sec1L34B45

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

theorem stmt5_1_14_qBound_of_d310
    (h5114 : Stmt5_1_14_first) (h510 : Stmt5_1_10) (h520 : Stmt5_1_20) (h521 : Stmt5_1_21)
    (hF : L2TorusFact) (hD : D310L34Fact) : Stmt5_1_14_qBound :=
  stmt5_1_14_qBound_of_inputs h5114 h510 h520 h521 hF hD B45L34.b45L34Fact_holds

end CFSG.Quasithin.H13
