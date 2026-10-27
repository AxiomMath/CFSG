module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem7U
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem7Lists
public import CFSG.Quasithin.Vol2.GoldschmidtTD32
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE22NoNProved
public import CFSG.Quasithin.H13.NQCatLemma128One

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

theorem stmt12_2_7_of_unique
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h6220 : Stmt6_2_20) (h37 : A37ForSQTK)
    (h3214 : Stmt3_2_14) : Stmt12_2_7 :=
  stmt12_2_7_of_lists h331 h1222 stmt3_2_3_proved h6220 e22StatementNoN_proved h37
    NQCat.lemma128One_holds (lem1227NotQuasisimple_of_unique h331 h3214)

end CFSG.Quasithin.H13
