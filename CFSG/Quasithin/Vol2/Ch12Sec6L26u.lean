module

public import CFSG.Quasithin.Vol2.Ch12Sec6L26t

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits S126

theorem lemma12_6_26_of (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h1224 : Lemma12_6_24)
    (h1226' : Stmt12_2_6) (h1261 : Lemma12_6_1) (h1262 : Theorem12_6_2)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (hComp : FactComp12626)
    (hD : FactHatA7Loc12626) (hE : FactM22Twelve12626) (hF : FactL211Loc12626) :
    Lemma12_6_26 := by
  intro G _ _ T L V _ F hH hZ H hHz
  by_contra hnab
  obtain ⟨-, h25b, h25c⟩ := lemma12_6_25_of h1224 G T L V F hH hZ H hHz
  have hV : ¬ V ≤ pCoreOf 2 H := fun hle => hnab (h25c.mp (h25b.mp hle))
  obtain ⟨v, hv, hvQ⟩ := Set.not_subset.mp hV
  obtain ⟨h, -, -, -, -⟩ := S126L26.setup126 h1224 F hH hZ hHz
  have hvH : v ∈ H := h.V_le_H hv
  have hyp := hH.hyp
  have : IsSimpleGroup G := hyp.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat hyp.nonabelian hyp.qtke).1
  have hQ := Vol2Native.sqtkHypCat_quotient_of_pCoreOf_ne_bot hloc hHz.1.2
  obtain ⟨K, hK, P, hPL, hP3, -, hc⟩ :=
    S126L26.exists_conf h331 h1222 h1224 h37 h38 F hH hZ hHz hv hvH hvQ
  rcases hComp _ _ _ _ _ _ hQ hc with hA7 | hM22 | hL211
  · exact S126L26.false_of_a7 h1222 h1224 h1261 hD F hH hZ hHz hQ.sqt hc hA7
  · exact S126L26.false_of_m22 h1224 h1226' h1262 hE F hH hZ hHz hv hvH hvQ hM22 hc.v_norm hc.v_nc
  · exact S126L211.false_of_l211 h1222 h1224 h1226' h1262 hF F hH hZ hHz hQ.sqt hv hvH hvQ hK hPL
      hP3 hc hL211

end CFSG.Quasithin.H13
