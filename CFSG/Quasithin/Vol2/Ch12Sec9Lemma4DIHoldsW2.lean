module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4IDMain
public import CFSG.Quasithin.Vol2.Ch12Sec8OneThirteenFive
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIF0
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIF1
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIF3
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIF5
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIFinal

public section

namespace CFSG.Quasithin.H13.C1294

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Quasithin.H13

theorem case1294FiveID_ofW2 (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) (h1228 : Stmt12_2_8)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h12810 : Lemma12_8_10)
    (h12813 : Lemma12_8_13) (h1264 : Stmt12_6_34) (h1292 : Lemma12_9_2)
    (hov : Lemma12_9_4Overgroup) : Case1294FiveID :=
  case1294FiveID_of_five h1222 h1264
    (lemma12_8_13_five_of h1222 h12213 h1228 h37 h38 h39 h12810 h12813) h1292 hov

theorem case1294FiveDI_holds_ofW2 (F4 : FactF4) (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13)
    (h1228 : Stmt12_2_8) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h12810 : Lemma12_8_10) (h12813 : Lemma12_8_13) (hID : Case1294FiveID) : Case1294FiveDI :=
  case1294FiveDI_ofW_five factF0_holds factF1_holds factF2_holds factF3_holds F4 factF5_holds
    h1222 h12213 h12810 h12813
    (lemma12_8_13_five_of h1222 h12213 h1228 h37 h38 h39 h12810 h12813) hID

end CFSG.Quasithin.H13.C1294

end
