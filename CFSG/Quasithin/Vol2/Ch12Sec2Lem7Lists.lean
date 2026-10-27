module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem7
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem7NoN

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

theorem stmt12_2_7_of_lists
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3)
    (h6220 : Stmt6_2_20) (hE22 : E2.E22StatementNoN) (h37 : A37ForSQTK) (h128 : Lemma128One)
    (hNQ : Lem1227NotQuasisimple) : Stmt12_2_7 :=
  stmt12_2_7_of h331 h1222 h323 h6220 hE22 h37 h128 lem1227ListEq_holdsNoN lem1227ListLt_holdsNoN
    hNQ

end CFSG.Quasithin.H13
