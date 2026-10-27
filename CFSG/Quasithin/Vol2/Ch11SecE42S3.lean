module

public import CFSG.Quasithin.Vol2.Ch11SecE42S3c
public import CFSG.Quasithin.Vol2.Ch11SecE42S3Obl
public import CFSG.Quasithin.Vol2.Ch11SecE42Obl
public import CFSG.Quasithin.Vol2.Ch11SecE42S3b

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

theorem obl11_4_2S3_of (hF : Facts42) (hS : Facts42S3) (hF43 : Facts43) (hP : SecB.PointFacts)
    (hN : SecA.NatFacts) (hPar : ParInFacts) (hM24 : IsSimpleGroup ↥NativeSporadic.M24)
    (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat)
    (h39 : QuasithinUnique.Vol2Native.A39ForSQTKCat) (h325 : Stmt3_2_5) (h328 : Stmt3_2_8)
    (h701 : Stmt7_0_1) (hFSU : Ch10.StmtFSUChoice) (h1102 : Stmt11_0_2) (h1110 : Stmt11_1_0)
    (h1111 : Stmt11_1_1) (h1141 : Stmt11_4_1) (hLie : Obl11_4_2S3Lie) (hA7 : Obl11_4_2S3A7) :
    Obl11_4_2S3 := by
  intro G _ _ T L I n V₁ z hc hmax
  have hJ := not_thompsonJ_le hF hF43 hN hPar h37 h38 h39 h1102 h1110 h1111 h1141 hc hmax
  rcases kz_type hF hS hF43 hP hM24 h37 h39 h325 h328 h701 hFSU h1102 h1110 h1111 h1141 hc hmax
    with hL | ⟨hn2, hA⟩
  · exact hLie G T L I n V₁ z hc hmax hJ hL
  · exact hA7 G T L I n V₁ z hc hmax hn2 hJ hA

end CFSG.Quasithin.Vol2.Ch11.SecE
