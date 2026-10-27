module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K326P1Cover
public import CFSG.LocalAnalysis.UniquenessCase.UC1K326P1Norm
public import CFSG.LocalAnalysis.UniquenessCase.UC1K326P1Four

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326

open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G] {n : ℕ} {P : Subgroup G}

theorem comp_pRank_two_or_three (h : Hyp326 G n P) {L : Subgroup G}
    (hL : CFSG.Open.IsComponentOf L ⊤)
    (hz : Subgroup.center ↥L ≠ ⊥) :
    CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) = 2 ∨ CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) = 3 := by
  have hT := comp_isSylowOf_inf h.sylow hL
  have hnc := comp_sylow_not_commutative hL.2.2 (comp_center_isPGroup h.core hL) hz hT
  obtain ⟨E, hET, hE, hE9⟩ := exists_elemAbelian_nine hT.isPGroup hnc
  have h2 : 2 ≤ CFSG.Open.pRank 3 (L : Subgroup G) :=
    CFSG.SectionRank.le_pRank (by norm_num) (hET.trans inf_le_right) hE
      (by rw [hE9]; norm_num)
  have h3 : CFSG.Open.pRank 3 (L : Subgroup G) ≤ 3 :=
    (CFSG.SectionRank.pRank_mono (by norm_num) le_top).trans (pRank_top_le_three h)
  rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
  omega

theorem comp_classify (h334 : K334Cover) (h : Hyp326 G n P)
    {L : Subgroup G} (hL : CFSG.Open.IsComponentOf L ⊤) (hz : Subgroup.center ↥L ≠ ⊥) :
    IsSL3pi ↥L ∨ ExcludedCover ↥L :=
  h334 ↥L hL.2.2 (comp_isCatalogGroup h.kgroup hL) (comp_center_isPGroup h.core hL)
    (comp_pRank_two_or_three h hL hz) hz

theorem K326P1_of_inputs (h334 : K334Cover) (hat : K326AtlasData) : K326P1 := by
  intro G _ _ hK hc n hn P hP e hz L hL
  have h : Hyp326 G n P := ⟨hK, hc, hn, hP, e, hz⟩
  rcases comp_classify h334 h hL (comp_center_ne_bot h hL) with hs | hex
  · exact hs
  · exact (excluded_cover_false hat h hL (comp_normalized h hL) hex).elim

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326
