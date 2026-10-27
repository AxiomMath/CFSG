module

public import CFSG.Quasithin.Vol2.Ch12Sec6Final
public import CFSG.Quasithin.Vol2.Ch12Sec6L23a

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S126
open scoped IsMulCommutative

theorem lemma12_6_29_of (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h3228 : Stmt3_2_2_eight)
    (h1262 : Theorem12_6_2) (h1219 : Lemma12_6_19) (h1228 : Lemma12_6_28) : Lemma12_6_29 := by
  intro G _ _ T L V _ F hH hZ H₀ hH₀ hn
  obtain ⟨hVT, hTV, hVe, hV1, -⟩ := S126L23a.basics h1222 F hH
  have hw := (h1228 G T L V F hH hZ).2.2.2.2
  have hr := (S126L20.rParam_bounds h331 h1222 h1262 F hH (h1219 G T L V F hH).1).1
  have h1 : 1 < min (E3.wParam T V) (E3.rParam V) :=
    lt_min hw (lt_of_lt_of_le (by norm_num) hr)
  have hCH : H₀ ⊓ Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans
      (S126L20c.normalizer_V_le h331 h1222 F hH))
  have hS := S126L23a.isSylowIn_of_le hH hH₀.1
  have hT : E3.HypE322 T V := ⟨S126L23a.isSylowIn_top hH, hVT, hTV⟩
  have hM := S126L23a.isUniqueM_Q h331 h3228 h1222 F hH
  rcases hn with hn | hsol
  · exact E3.e3_35_one hVe hV1 hT hM hS hCH inf_le_left (by rw [hn]; exact h1)
  · exact E3.e3_35_one_solvable hVe hV1 hT hM hS hCH inf_le_left hsol h1

end CFSG.Quasithin.H13
