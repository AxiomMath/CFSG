module

public import CFSG.Quasithin.Vol2.Ch10SecD12
public import CFSG.Quasithin.Vol2.Ch10SecDMain
public import CFSG.Quasithin.Vol2.Ch10SecQ6A5c
public import CFSG.Quasithin.Vol2.Ch10SecQ6O4e
public import CFSG.Quasithin.Vol2.Ch10SecQ6WWd
public import CFSG.Quasithin.Vol2.Ch10SecQ6SzB
public import CFSG.Quasithin.Vol2.Ch10SecQ6Wr
public import CFSG.Quasithin.Vol2.Ch10SecQ6Nrm

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Quasithin.E3

theorem stmt10_2_12_of' (h331 : Stmt3_3_1)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (hI16 : ASInputs.AS_I_1_6)
    (h1011 : Stmt10_1_1) (h1012 : Stmt10_1_2) (h1013 : Stmt10_1_3) (h1027 : Stmt10_2_7)
    (h1029 : Stmt10_2_9) (h10210 : Stmt10_2_10) (h10211 : Stmt10_2_11) : Stmt10_2_12 :=
  stmt10_2_12_of fact12L2 fact12A5 fact12O4 fact12WW fact12Sz h331 h37 h38 hI16 h1011 h1012
    h1013 h1027 h1029 h10210 h10211

theorem stmt10_3_1_of_inputs' (h331 : Stmt3_3_1) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hI16 : ASInputs.AS_I_1_6) (h1012 : Stmt10_1_2)
    (h1023 : Stmt10_2_3) (h1028 : Stmt10_2_8) (h1029 : Stmt10_2_9) (h10210 : Stmt10_2_10)
    (h10213 : Stmt10_2_13) : Stmt10_3_1 :=
  stmt10_3_1_of_inputs factAParamWreath h331 h37 h38 hI16 h1012 h1023 h1028 h1029 h10210 h10213

theorem stmtClose10_of_inputs' (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h1023 : Stmt10_2_3) (h1024 : Stmt10_2_4)
    (h10211 : Stmt10_2_11) (h10213 : Stmt10_2_13) (h1031 : Stmt10_3_1) (h1032 : Stmt10_3_2) :
    StmtClose10 :=
  stmtClose10_of_inputs factPSL2NormA5 factAutSL h37 h38 h1023 h1024 h10211 h10213 h1031 h1032

end CFSG.Quasithin.Vol2.Ch10.SecD
