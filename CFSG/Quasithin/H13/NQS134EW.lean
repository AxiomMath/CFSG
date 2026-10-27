module

public import CFSG.Quasithin.H13.NQS134EV
public import CFSG.Quasithin.H13.U3S1347Fin
public import CFSG.Quasithin.H13.U3S1348T
public import CFSG.Quasithin.H13.U3S135W
public import CFSG.Quasithin.H13.U3L134
public import CFSG.Quasithin.H13.U3L134W
public import CFSG.Quasithin.H13.GoldschmidtSp62Involutions
public import CFSG.Quasithin.H13.GoldschmidtSp62Transvections
public import CFSG.Quasithin.H13.KGFactF618Big

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

theorem stmt13_4_1_assembled
    (h1332 : Stmt13_3_2) (h1222 : Stmt12_2_2) (h1226 : Stmt12_2_6) (h1228 : Stmt12_2_8)
    (h12213 : Stmt12_2_13) (h331 : Stmt3_3_1) (h1327 : A5.Stmt13_2_7)
    (hL1 : U3.Stmt13_2_2_9L1) (h13316 : Stmt13_3_16) (hC58 : TheoremC58) (h317 : AS317Sylow)
    (h56 : AsB56) (hC137 : U3.C137StatementFiveZ) (hedge : GoldschmidtEdgeBoundS3)
    (hF : F6.TheoremF618Cat) (h37 : Vol2Native.A37ForSQTKCat)
    (h39 : Vol2Native.A39ForSQTKCat) : A6.Stmt13_4_1 := by
  have hBig : A5.FactF618Big := A5.factF618Big_holds
  have h135 : A6.Stmt13_3_5 := U3.stmt13_3_5_of_1332 h1332 h12213 h331 h1327
  have h1334 : A6.Stmt13_3_4 := U3.stmt13_3_4_of h1332
  have h1337 : A6.Stmt13_3_7 := U3.stmt13_3_7_of h1332 h1228
  have h1338 : A6.Stmt13_3_8 := U3.stmt13_3_8_holds h1332
  have h139 : A6.Stmt13_3_9 := U3.stmt13_3_9_of_1332 h1332 h1226 h1228 hL1
  have h44 : U3.Stmt13_4_4 := U3.stmt13_4_4_of h1222 h1332 h1226 h1228 h1338 hL1
  have h1345 : Stmt13_4_5 := stmt13_4_5_of h1332 h13316 h1334 h1338
  have h1348 : U3.Stmt13_4_8 :=
    U3.stmt13_4_8_of hC137 h1332 h331 h1222 h44 hC58 h317 h56 h1228 h139
  have h1347One : U3.Stmt13_4_7One :=
    U3.stmt13_4_7One_of hedge h1332 h1228 hC58 h317 h56 h135 h1345 hF hBig
  have h1347 : U3.Stmt13_4_7L2 :=
    U3.stmt13_4_7L2_holds hC137 hedge h1332 h1228 hC58 h317 h56 h135 h1345 hF hBig h1222 h139
      h37 h39
  have hloc : A6.Input1349Local :=
    U3.input1349Local_of h1222 h1332 hC58 h317 h56 h1345 h1347 h1348
      U3.sp62InvolutionsIntoCJ_of U3.sp62TransvectionProduct_of
  have h1349 : A6.Stmt13_4_9 :=
    A6.prop_13_4_9 h1332 h1222 (A6.input1349_of_local h1222 hloc)
  have h13410 : A6.Stmt13_4_10_17 :=
    stmt13_4_10_17_of_inputs hC137 h1332 h1228 hC58 h317 h56 h1222 h1347One h1347 h1348 h13316
      h1334 h1337 h1338 h331
  exact A6.stmt13_4_1_of_inputs h1332 h135 h1349 h13410

end CFSG.Quasithin.H13.NQS134
