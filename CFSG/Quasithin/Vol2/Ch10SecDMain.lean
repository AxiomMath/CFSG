module

public import CFSG.Quasithin.Vol2.Ch10SecDFactVXE
public import CFSG.Quasithin.Vol2.Ch10SecDVE4
public import CFSG.Quasithin.Vol2.Ch10SecDXI6
public import CFSG.Quasithin.Vol2.Ch10SecDMP2
public import CFSG.Quasithin.Vol2.Ch10SecDTL4
public import CFSG.Quasithin.Vol2.Ch10SecDWreathD
public import CFSG.Quasithin.Vol2.Ch10SecD31
public import CFSG.Quasithin.Vol2.Ch10SecDClose

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique

theorem stmt10_2_11_of_inputs
    (hG31 : ASInputs.AS_G_3_1_O2) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h1013 : Stmt10_1_3) (h1024 : Stmt10_2_4)
    (h1029 : Stmt10_2_9) : Stmt10_2_11 :=
  stmt10_2_11_of h37 h38 h1013 h1024 h1029 (factXIrred h37 h38) (factXThree_of h37 h38)
    (factVEIrred h37 h38) (factVXE_of h37 h38) (factMaxP h37 h38)
    (factTransvList_of hG31 h37 h38 h1029)

theorem stmt10_3_1_of_inputs (hA : FactAParamWreath) (h331 : Stmt3_3_1)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (hI16 : ASInputs.AS_I_1_6)
    (h1012 : Stmt10_1_2) (h1023 : Stmt10_2_3) (h1028 : Stmt10_2_8) (h1029 : Stmt10_2_9)
    (h10210 : Stmt10_2_10) (h10213 : Stmt10_2_13) : Stmt10_3_1 :=
  stmt10_3_1_of hA factSymFiveWrTwo h331 h37 h38 hI16 h1012 h1023 h1028 h1029 h10210 h10213

theorem stmtClose10_of_inputs (hA : FactPSL2NormA5) (hAut : FactAutSL)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (h1023 : Stmt10_2_3)
    (h1024 : Stmt10_2_4) (h10211 : Stmt10_2_11) (h10213 : Stmt10_2_13) (h1031 : Stmt10_3_1)
    (h1032 : Stmt10_3_2) : StmtClose10 :=
  stmtClose10_of factSymFiveWrTwo hA hAut (factMaxP h37 h38) h37 h38 h1023 h1024 h10211 h10213
    h1031 h1032

end CFSG.Quasithin.Vol2.Ch10.SecD
