module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalL2Two
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeLocalNormal

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

theorem stmt5_2_2_of_inputs
    (h515 : Stmt5_1_5) (h516 : Stmt5_1_6) (h510 : Stmt5_1_10) (h5111 : Stmt5_1_11)
    (h5113 : Stmt5_1_13C) (h5114 : Stmt5_1_14) (hU3 : FactU3Cover) (hF : FactL2LieParabolic)
    (hRL : RankOneListedFacts.{0}) (hbot : Stmt5_2_2_bot) (hne : Stmt5_2_2_ne) : Stmt5_2_2C :=
  stmt5_2_2_of Vol2Native.a39ForSQTKCat_proved h510 h516 h5113 h5114
    (stmt5_2_1_of h510 h5111 (stmt5_2_1_par_of_inputs hU3 hF hRL h515 h510)) l2TorusFact
    (ch5L2ChoiceExists_of_inputs h510 hF) hbot hne

end CFSG.Quasithin.H13
