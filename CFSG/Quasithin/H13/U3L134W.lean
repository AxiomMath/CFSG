module

public import CFSG.Quasithin.H13.U3L134K
public import CFSG.Quasithin.H13.U3L139S

public section

namespace CFSG.Quasithin.H13.U3

open CFSG.Open CFSG.Blueprint CFSG.Quasithin

theorem stmt13_3_8_holds
    (h1332 : Stmt13_3_2) : A6.Stmt13_3_8 :=
  stmt13_3_8_of h1332 (stmt13_3_4K_of h1332)

theorem stmt13_3_9_of_1332
    (h1332 : Stmt13_3_2) (h1226 : Stmt12_2_6)
    (h1228 : Stmt12_2_8) (hL1 : Stmt13_2_2_9L1) : A6.Stmt13_3_9 :=
  stmt13_3_9_of h1332 h1226 h1228 (stmt13_3_8_holds h1332) hL1

end CFSG.Quasithin.H13.U3
