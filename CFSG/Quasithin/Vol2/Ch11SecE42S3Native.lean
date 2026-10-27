module

public import CFSG.Quasithin.Vol2.Ch11SecE42S3

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

theorem obl11_4_2S3_of_native
    (hF : Facts42) (hS : Facts42S3) (hF43 : Facts43)
    (hP : SecB.PointFacts) (hN : SecA.NatFacts) (hPar : ParInFacts)
    (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat)
    (h39 : QuasithinUnique.Vol2Native.A39ForSQTKCat) (h325 : Stmt3_2_5) (h328 : Stmt3_2_8)
    (h701 : Stmt7_0_1) (hFSU : Ch10.StmtFSUChoice) (h1102 : Stmt11_0_2) (h1110 : Stmt11_1_0)
    (h1111 : Stmt11_1_1) (h1141 : Stmt11_4_1) (hLie : Obl11_4_2S3Lie) (hA7 : Obl11_4_2S3A7) :
    Obl11_4_2S3 :=
  obl11_4_2S3_of hF hS hF43 hP hN hPar CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2 h37 h38 h39
    h325 h328 h701 hFSU h1102 h1110 h1111 h1141 hLie hA7

end CFSG.Quasithin.Vol2.Ch11.SecE
