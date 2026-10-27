module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1R925Star
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1R925Strong
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1R925Struct

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem r925_centralizer_ne_top (D : Data G) {z : G} (hz : z ≠ 1) :
    centralizer ({z} : Set G) ≠ ⊤ := by
  haveI : IsSimpleGroup G := D.standing.simple
  exact CFSG.RankThree.PartOne.centralizer_singleton_ne_top_of_simple D.standing.nonab hz

theorem r925_kgroup_bar2 (D : Data G) {H : Subgroup G} (hH : H ≠ ⊤) :
    CFSG.Open.IsKGroup (Bar2 H) := by
  have hKH : CFSG.Open.IsKGroup ↥H := CFSG.Open.IsKProper.isKGroup D.standing.kProper H hH
  exact CFSG.Open.IsKGroup.quotient hKH (CFSG.pCore 2 ↥H)

theorem r925_bar2_o2 (H : Subgroup G) : CFSG.pCore 2 (Bar2 H) = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot (H := ↥H) (p := 2)

theorem r925_pRank_bar2 {H : Subgroup G} {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    CFSG.Open.pRank q (⊤ : Subgroup (Bar2 H)) ≤ CFSG.Open.pRank q H := by
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (H := H)]
  exact r925_pRank_quotient_le (CFSG.pCore 2 ↥H) hq (r925_pCore_two_orderOf hq hq2)

theorem r925_hyp_le {D : Data G} {L P X H Y : Subgroup G} {z : G} (h : R925Hyp D L P X H Y z) :
    Y ≤ L ∧ Y ≤ H ∧ L ≤ D.M ∧ pCoreOf 2 H ≤ D.M := by
  have hYX : Y ≤ X := by
    rw [h.y_eq]
    exact (perfectCore_le (H ⊓ X)).trans inf_le_right
  have hYP : Y ≤ P := by
    calc Y ≤ X := hYX
      _ = perfectCore P := h.x_eq
      _ ≤ P := perfectCore_le P
  refine ⟨hYP.trans h.parabolic.1, ?_, CFSG.Open.IsSubnormal.le h.mem_calC.1, ?_⟩
  · rw [h.y_eq]
    exact (perfectCore_le (H ⊓ X)).trans inf_le_left
  · exact (r925_pCoreOf_le_of_sylow h.sylow).trans (le_trans inf_le_left D.sylowM.le)

theorem r925_descent (D : Data G) (h82 : F08.R82 D)
    {L P X H Y : Subgroup G} {z : G} (h : R925Hyp D L P X H Y z) :
    R925Ctx (Bar2 H) (starImg H Y) (starImg H (hConj H Y)) (starImg H D.M) := by
  obtain ⟨hYL, hYH, hLM, hQM⟩ := r925_hyp_le h
  have hSE := r925_strong_embed h82 h.mem_calC h.isU4
  have hHne : H ≠ ⊤ := h.h_eq ▸ r925_centralizer_ne_top D h.z_ne_one
  have hYperf : commutator ↥Y = ⊤ := by
    rw [h.y_eq]
    exact r925_commutator_perfectCore _
  exact
    { kgroup := r925_kgroup_bar2 D hHne
      o2_eq_bot := r925_bar2_o2 H
      rank_three := (r925_pRank_bar2 Nat.prime_three (by norm_num)).trans h.rank_h.le
      rank_gt_three := fun q hq hq3 => (r925_pRank_bar2 hq (by omega)).trans (h.rank_h_gt q hq hq3)
      y_cover := r925_perfA5Cover_starImg hYH (r925_perfA5Cover_of_e16a5 hYL hYperf h.e16a5)
      k_eq := r925_starImg_hConj hYH
      y_le := r925_starImg_mono (hYL.trans hLM)
      m_catalogue := r925_kGroupNonab_starImg H D.M (isoInvariant_dvdOrThreeFree 51840)
        (r925_m_catalogue D h.mem_calC h.isU4 h.rank_m)
      m_odd := r925_odd_index_starImg h.odd_relIndex
      m_normalizer := r925_normalizer_starImg hQM fun D' hD' hD'3 =>
        r925_normalizer_le hSE hD' hD'3
      m_ne_top := fun htop => h.not_le (r925_le_of_starImg_eq_top hQM htop) }

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
