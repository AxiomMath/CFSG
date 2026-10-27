module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.E3Weak
public import CFSG.Quasithin.Vol2.Ch12Sec7Orb

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.LieType.BorelTits E3
open scoped IsMulCommutative

namespace S127

variable {G : Type} [Group G] [Finite G]

theorem isPGroup_V {T L V : Subgroup G} (h : Hyp1271 G T L V) : IsPGroup 2 V :=
  fun v => ⟨1, Subtype.ext (by simpa using sq_eq_one_of_mem h.hyp v.2)⟩

theorem normalizer_V_le (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) {T L V : Subgroup G}
    (h : Hyp1271 G T L V) :
    Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  have hyp := h.hyp
  obtain ⟨-, -, hTV⟩ := card_eq_of_1222 h1222 h
  have h3 := (h331 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow).2 L hyp.maximal
    hyp.quasisimple
  rw [hyp.conjClosure_eq] at h3
  obtain ⟨⟨-, -, huniq⟩, -⟩ := h3
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le hyp.irrPlus.2.2.1 hTV
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge (L := Subgroup.normalizer (V : Set G))
    ⟨V, hyp.irrPlus.2.1, isPGroup_V h, rfl⟩
  have hM'eq : M' = Subgroup.normalizer (L : Set G) := huniq M' hM' (hLTV.trans hle)
  exact hM'eq ▸ hle

theorem exists_conj_not_le (h11 : Lemma12_7_11) {T L V : Subgroup G} {t z : G}
    (hS : Setting1274 G T L V t z) {H : Subgroup G}
    (hHs : IsHStar T (Subgroup.normalizer (L : Set G)) H) :
    ∃ g : G, conjSubgroup V g ≤ T ⊓ Subgroup.centralizer (V : Set G) ∧
      ¬ conjSubgroup V g ≤ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hW0, -, hNW⟩ := h11 G T L V t hS.toSetting1273
  have hT := hS.hyp.hyp.sylow
  have hS' : IsSylowIn 2 T H :=
    ⟨hHs.1.1, hT.1, fun h => hT.2 (h.trans (Subgroup.relIndex_dvd_index_of_le hHs.1.1))⟩
  by_contra hne
  push Not at hne
  have hWle : wClos V 0 T ≤ pCoreOf 2 H := by
    refine iSup₂_le fun A hA => ?_
    obtain ⟨-, g, hAg, hm⟩ := id hA
    have hAeq : A = conjSubgroup V g :=
      (mQuot_eq_zero_iff (isPGroup_conjSubgroup (isPGroup_V hS.hyp) g) hAg).1 hm
    have hle := (le_wClos hA).trans hW0
    rw [hAeq] at hle ⊢
    exact hne g hle
  have hN := e3_15_normalizer hS' (pCoreOf_le 2 H) (pCoreOf_isPGroup 2 H) hWle
  exact hHs.2.1 ((le_normalizer_pCoreOf 2 H).trans (hN.trans hNW))

end S127

end CFSG.Quasithin.H13
