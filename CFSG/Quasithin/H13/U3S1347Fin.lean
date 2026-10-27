module

public import CFSG.Quasithin.H13.U3S1347Asm
public import CFSG.Quasithin.H13.U3S13472F
public import CFSG.Quasithin.H13.NQS134YC

public section

namespace CFSG.Quasithin.H13.U3

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

theorem stmt13_4_7L2_holds (hC137 : C137StatementFiveZ)
    (hedge : GoldschmidtEdgeBoundS3) (h1332 : Stmt13_3_2) (h1228 : Stmt12_2_8)
    (hC58 : TheoremC58) (h317 : AS317Sylow) (h56 : AsB56) (h135 : A6.Stmt13_3_5)
    (h1345 : NQS134.Stmt13_4_5) (hF : F6.TheoremF618Cat) (hBig : A5.FactF618Big)
    (h1222 : Stmt12_2_2) (h139 : A6.Stmt13_3_9) (h37 : Vol2Native.A37ForSQTKCat)
    (h39 : Vol2Native.A39ForSQTKCat) : Stmt13_4_7L2 :=
  stmt13_4_7L2_of hC137 hedge h1332 h1228 hC58 h317 h56 h135 h1345 hF hBig h1222 h139
    (NQS134.stmt13473NonSolv_of hC137 h1332 h1228 hC58 h317 h56 h1345 hF hBig)
    (s1347_two_forall hC137 hedge h1332 h1228 hC58 h317 h56 h135 h1345 hF hBig h37 h39)

end CFSG.Quasithin.H13.U3
