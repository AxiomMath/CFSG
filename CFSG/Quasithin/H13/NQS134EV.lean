module

public import CFSG.Quasithin.H13.NQS134EU

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

theorem stmtEnd134_of_inputs (hC137 : U3.C137StatementFiveZ)
    (h1332 : Stmt13_3_2) (h1228 : Stmt12_2_8) (hC58 : TheoremC58) (h317 : AS317Sylow)
    (h56 : AsB56) (h1222 : Stmt12_2_2) (h1347One : U3.Stmt13_4_7One)
    (h1347 : U3.Stmt13_4_7L2) (h1348 : U3.Stmt13_4_8)
    (h13316 : Stmt13_3_16) (h1334 : A6.Stmt13_3_4) (h1337 : A6.Stmt13_3_7)
    (h1338 : A6.Stmt13_3_8) (h331 : Stmt3_3_1) : StmtEnd134 :=
  stmtEnd134_of hC137 h1332 h1228 hC58 h317 h56 h1222 h1347One h1347 h1348
    (stmt13_4_5_of h1332 h13316 h1334 h1338)
    (stmt13_4_6_of h1222 h1332 h13316 h1334 h1337 h1338 hC58 h317) h331

theorem stmt13_4_10_17_of_inputs
    (hC137 : U3.C137StatementFiveZ) (h1332 : Stmt13_3_2) (h1228 : Stmt12_2_8)
    (hC58 : TheoremC58) (h317 : AS317Sylow) (h56 : AsB56) (h1222 : Stmt12_2_2)
    (h1347One : U3.Stmt13_4_7One) (h1347 : U3.Stmt13_4_7L2) (h1348 : U3.Stmt13_4_8)
    (h13316 : Stmt13_3_16)
    (h1334 : A6.Stmt13_3_4) (h1337 : A6.Stmt13_3_7) (h1338 : A6.Stmt13_3_8)
    (h331 : Stmt3_3_1) : A6.Stmt13_4_10_17 :=
  stmt13_4_10_17_of h1332 (stmtEnd134_of_inputs hC137 h1332 h1228 hC58 h317 h56 h1222 h1347One h1347
    h1348 h13316 h1334 h1337 h1338 h331)

end CFSG.Quasithin.H13.NQS134
