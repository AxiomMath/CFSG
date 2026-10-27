module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R847FieldsCZ
public import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem thin8_of_isL2_or_isSz {L : Subgroup G} {f : ℕ}
    (hL : IsL2 (Bar2 L) f ∨ IsSz (Bar2 L) f) : F08.Thin8 L := by
  intro p hp hp2
  rw [← pRank_bar2_eq_of_odd hp hp2]
  exact pRank_le_one_of_isL2_or_isSz hL hp hp2

theorem not_thin8_of_isSU3 {L : Subgroup G} {n : ℕ} (h : IsSU3 (Bar2 L) n) (hn : Odd n) :
    ¬ F08.Thin8 L := by
  intro hthin
  have h3 : CFSG.Open.pRank 3 L ≤ 1 := hthin 3 Nat.prime_three (by norm_num)
  rw [← pRank_bar2_eq_of_odd Nat.prime_three (by norm_num)] at h3
  have h2 := two_le_pRank_three_of_isSU3 h hn
  omega

theorem Ctx23L.normalizer_zpowers_le_M {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (h1930 : H1930 D) (h4 : S23_4 D Ch) (h847 : R847ThinCZ D) {K : Subgroup G}
    (hK : K ∈ calC D.M) {f : ℕ} (hKf : IsL2 (Bar2 K) f ∨ IsSz (Bar2 K) f) {a : G}
    (haK : a ∈ K) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (har : orderOf a = r) :
    Subgroup.normalizer (Subgroup.zpowers a : Set G) ≤ D.M :=
  c.normalizer_zpowers_le_M_of_r847ThinCZ h1930 h4 h847 hK
    (thin8_of_isL2_or_isSz hKf) haK hr hr2 har

end CFSG.LocalAnalysis.UniquenessCase.UC22
