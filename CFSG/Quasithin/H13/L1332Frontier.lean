module

public import CFSG.Quasithin.H13.L1332Wired
public import CFSG.Quasithin.H13.LocDblSporadic
public import CFSG.Quasithin.H13.FiveQuotients
public import CFSG.Quasithin.H13.L32NoIrrFourProof
public import CFSG.Quasithin.Vol2.GoldschmidtTD32

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

theorem stmt13_3_2_of_frontier
    (h137 : Stmt13_1_7) (h1222 : Stmt12_2_2) (h1242 : Stmt12_4_2) (h1271 : Stmt12_7_1)
    (hA7 : StmtFiveA7Elim) (hLin : LinearSelectedNaturalConfigurationProducer) : Stmt13_3_2 :=
  stmt13_3_2_of_open LocDbl.local_double_embedding_exclusion h137
    (stmt13_1_2_three_of_inputs h1222 hA7 hLin) stmt3_2_3_proved h1222 h1242 h1271
    l32NoIrrFour_holds

end CFSG.Quasithin.H13
