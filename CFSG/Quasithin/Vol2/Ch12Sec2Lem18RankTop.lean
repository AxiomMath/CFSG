module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem18Rank
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem18
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem17
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem16Two

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

theorem stmt12_2_18_of_A8Zv
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3) (hzv : Lem12216A8Zv)
    (h1227 : Stmt12_2_7) : Stmt12_2_18 :=
  stmt12_2_18_of h331 h1222 h323 (stmt12_2_16_of_A8Zv h1222 h331 h323 hzv)
    (stmt12_2_17_of (stmt12_2_16_of_A8Zv h1222 h331 h323 hzv) h1222 h323)
    (lem12218TwoRank_of h331 h1222 h323 h1227)

end CFSG.Quasithin.H13
