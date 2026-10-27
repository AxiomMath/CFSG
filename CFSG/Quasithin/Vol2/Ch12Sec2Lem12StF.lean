module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem12StC
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem12StE
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem12Simp

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative

theorem stabSimple12_2_12 :
    StabSimple12_2_12 := by
  intro G _ _ L V _ hV2 hLV hq hO2 hirr hmod v hv hv1 hperf hK2 hVL
  rcases hmod with ⟨n, hn, -, hbn⟩ | ⟨he3, -, -⟩ | ⟨he5, hcard, hirr10⟩ |
    ⟨n, -, -, -, halt⟩ | ⟨hcard4, φ, hφ, hker⟩ | ⟨-, hG2⟩ | ⟨hq', hZ3, he6, hCO, hcard6, -⟩
  · exact (Lem12St.false_of_natural hLV (by omega) hbn hv hv1 hK2 hVL).elim
  · exact Lem12St.simple_case_l3 hLV hV2 hq hO2 hirr he3 hv hv1 hperf hK2 hVL
  · exact (Lem12St.false_of_wedge hLV hV2 hO2 he5 hcard hirr10 hv hv1 hK2 hVL).elim
  · exact Lem12St.simple_case_alt hLV hV2 hq hO2 hirr halt hv hv1 hK2 hVL
  · exact Lem12St.simple_case_a7 hLV hV2 hcard4 φ hφ hker hv hv1 hperf hVL
  · exact Lem12St.simple_case_g2 hLV hV2 hq hO2 hirr hG2 hv hv1 hperf hK2 hVL
  · exact Lem12St.simple_case_hatA6 hLV hV2 hq' hZ3 he6 hCO hcard6 hv hv1 hperf hVL

theorem stmt12_2_12_of_inspection
    (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3)
    (h3228 : Stmt3_2_2_eight) : Stmt12_2_12 :=
  stmt12_2_12_of_stab h1222 h323 h3228 stabSimple12_2_12

end CFSG.Quasithin.H13
