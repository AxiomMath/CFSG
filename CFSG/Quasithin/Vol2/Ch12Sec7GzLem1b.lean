module

public import CFSG.Quasithin.Vol2.Ch12Sec7GzLem1
public import CFSG.Quasithin.Vol2.Ch12Sec7Mod10A
public import CFSG.Quasithin.Vol2.Ch12Sec7I77c

public section

namespace CFSG.Quasithin.H13.I1277

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S127
open scoped IsMulCommutative

theorem mEqNormV1277_of
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h1226 : Stmt12_2_6) : MEqNormV1277 := by
  intro G _ _ T L V t s
  have hVL : Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    S127.Mod.normalizer_V_le_M h331 h1222 s.d.hyp
  have hblk : IsHatA6Block L := s.isHatA6Block h1222
  obtain ⟨hOL, -, -, -⟩ :=
    (lemma12_7_6_of h1222 h1226 G T L V s.d.hyp hblk).2 (s.centralizer_L_eq_bot h331)
  have hLV : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (V : Set G) := by
    rw [← hOL]
    exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L
  exact le_antisymm hLV hVL

theorem gzNotLeM_of'
    (h71 : Setup1271) (h74 : Lemma12_7_4) (h125 : Lemma12_7_5) (h331 : Stmt3_3_1)
    (h1222 : Stmt12_2_2) (h1226 : Stmt12_2_6) (hK : KtLine1277) (hM : MLine1277) :
    GzNotLeM1277 :=
  gzNotLeM_of h71 h74 h125 hK hM (mEqNormV1277_of h331 h1222 h1226)

end CFSG.Quasithin.H13.I1277
