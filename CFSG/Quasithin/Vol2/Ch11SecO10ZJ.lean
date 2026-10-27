module

public import CFSG.Quasithin.Vol2.Ch11SecO10ZF
public import CFSG.Quasithin.Vol2.Ch11SecO10ZG
public import CFSG.Quasithin.Vol2.Ch11SecO10ZI
public import CFSG.Quasithin.Vol2.Ch11SecE42S3Obl

public section

namespace CFSG.Quasithin.Vol2.Ch11.O10

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 SecE

theorem obl11_4_2S3A7_of (hF : Facts42) (hS : Facts42S3) (hF43 : Facts43) (hF15 : SecA.Facts15)
    (hP : SecB.PointFacts) (hN : SecA.NatFacts) (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h39 : QuasithinUnique.Vol2Native.A39ForSQTKCat) (hFSU : Ch10.StmtFSUChoice)
    (h701 : Stmt7_0_1) (h325 : Stmt3_2_5) (h328 : Stmt3_2_8) (hB42 : AsB42) (h51 : AsB51)
    (h8 : Ch10.TmpL6_3_2_2_eight) (h1102 : Stmt11_0_2) (h1110 : Stmt11_1_0)
    (h1111 : Stmt11_1_1) (h1141 : Stmt11_4_1) : Obl11_4_2S3A7 := by
  intro G _ _ T L I n V₁ z hc hmax hn2 hJ hA7
  obtain ⟨I', hfsu⟩ :=
    exists_fsu_kz hF hS hF43 hP h1102 h1110 h1111 h1141 h37 h39 hFSU hc hmax
  rcases kz_a7_cases hF hS hF43 h701 h325 h328 h1102 h1110 h1111 h1141 hc hfsu hJ hA7 with
    ⟨-, -, hcomm, hnat⟩ | ⟨-, he, -⟩ | ⟨hcv, he, -, ⟨t, htT, htN⟩, hswap⟩
  · exact false_of_natural hF hS hF43 h701 hN hF15 hB42 h8 h1102 h1110 h1111 h1141 hc hn2 hfsu
      hJ hA7 hnat
  · exact false_of_autOn_sup hF hS hF43 h701 hN h1102 h1110 h1111 h1141 hc hn2 hfsu hJ hA7 he
  · obtain ⟨hsum, hinf, hni⟩ := hswap t htT htN
    exact false_of_sum hF hS hF43 h701 h51 h1102 h1110 h1111 h1141 hc hfsu hJ hcv he htT hsum
      hinf hni

end CFSG.Quasithin.Vol2.Ch11.O10
