module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154AssemblyCNLA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKSchur2
public import CFSG.GroupTheory.PRankBound

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s16h_nontrivial_of_isQuasisimple {X : Type} [Group X]
    (h : CFSG.Open.IsQuasisimple X) : Nontrivial X := by
  have hnc : ¬ IsMulCommutative X := by
    rw [← Subgroup.center_eq_top_iff]
    exact QuotientGroup.nontrivial_iff.mp h.2.toNontrivial
  rw [← not_subsingleton_iff_nontrivial]
  intro hsub
  exact hnc (IsMulCommutative.of_comm fun a b => by rw [Subsingleton.elim a b])

private theorem s16h_false_of_isCyclicOrd_of_quasisimple {X : Type} [Group X]
    (hq : CFSG.Open.IsQuasisimple X) {n : ℕ} (h : IsCyclicOrd X n) : False := by
  haveI : Group.IsPerfect X := Group.isPerfect_def.mpr hq.1
  haveI : Nontrivial X := s16h_nontrivial_of_isQuasisimple hq
  haveI : IsCyclic X := h.1
  exact Group.IsPerfect.not_isMulCommutative X inferInstance

private theorem s16h_false_of_isElemAbelianOfRank_of_quasisimple {X : Type} [Group X]
    (hq : CFSG.Open.IsQuasisimple X) {p r : ℕ} (h : IsElemAbelianOfRank p r X) : False := by
  haveI : Group.IsPerfect X := Group.isPerfect_def.mpr hq.1
  haveI : Nontrivial X := s16h_nontrivial_of_isQuasisimple hq
  obtain ⟨e⟩ := h
  exact Group.IsPerfect.not_isMulCommutative X
    (IsMulCommutative.of_comm fun a b => e.injective (by
      rw [map_mul, map_mul]
      exact mul_comm _ _))

private theorem s16h_pRank_le_one_of_isAlt_five_or_isL3_one {X : Type} [Group X] [Finite X]
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (h : IsAlt X 5 ∨ IsL3 X 1) :
    CFSG.Open.pRank q (⊤ : Subgroup X) ≤ 1 := by
  refine CFSG.GroupTheory.pRank_le_of_not_dvd_pow_succ (H := ⊤) hq ?_
  simpa [Subgroup.card_top] using s15k_schur2_not_sq_dvd h hq hq2

private theorem s16h_pRank_le_one_of_isL2 {X : Type} [Group X] [Finite X]
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {a : ℕ} (h : IsL2 X a) :
    CFSG.Open.pRank q (⊤ : Subgroup X) ≤ 1 :=
  UC22.pRank_le_one_of_isL2_or_isSz (Or.inl h) hq hq2

private theorem s16h_pRank_le_one_of_isOmegaMinus_four {X : Type} [Group X] [Finite X]
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {k : ℕ} (h : IsOmegaMinus X 4 k) (hk : 1 ≤ k) :
    CFSG.Open.pRank q (⊤ : Subgroup X) ≤ 1 :=
  UC22.pRank_le_one_of_isL2_or_isSz (Or.inl (S18.isL2_of_isOmegaMinus_four hk h)) hq hq2

private theorem s16h_false_of_pRank_top_le_one {X : Type} [Group X] [Finite X] {q : ℕ}
    {H : Subgroup X} (hle : CFSG.Open.pRank q (⊤ : Subgroup H) ≤ 1)
    (hr : 2 ≤ CFSG.Open.pRank q H) : False := by
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := q) H] at hr
  omega

theorem s16h_nonthin_shape_concl163 (D : Data G) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hs : 1 < s15 D.M V₀ V hV L)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hr : 2 ≤ CFSG.Open.pRank q (lBar V₀ V hV L))
    (h : Concl163 D V₀ V hV L) :
    UC22.IsAlt ↥(lBar V₀ V hV L) 6 ∨ UC22.IsAlt ↥(lBar V₀ V hV L) 7 ∨
      UC22.IsAlt ↥(lBar V₀ V hV L) 8 := by
  rcases h with h162 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12
  · exact s16h_nonthin_shape_concl162 D hV hs hcomp hq hq2 hr h162
  · obtain ⟨hL3, -, -⟩ := h1
    exact (s16h_false_of_pRank_top_le_one
      (s16h_pRank_le_one_of_isAlt_five_or_isL3_one hq hq2 (Or.inr hL3)) hr).elim
  · obtain ⟨-, -, hs1⟩ := h2
    exact absurd hs1 (by omega)
  · obtain ⟨hOm, -, -, -⟩ := h3
    exact (s16h_false_of_pRank_top_le_one
      (s16h_pRank_le_one_of_isOmegaMinus_four hq hq2 hOm (by norm_num)) hr).elim
  · obtain ⟨hL2, -, -⟩ := h4
    exact (s16h_false_of_pRank_top_le_one
      (s16h_pRank_le_one_of_isL2 hq hq2 hL2) hr).elim
  · obtain ⟨hshape, -⟩ := h5
    rcases hshape with ⟨hL3, -⟩ | ⟨hA5, -⟩
    · exact (s16h_false_of_pRank_top_le_one
        (s16h_pRank_le_one_of_isAlt_five_or_isL3_one hq hq2 (Or.inr hL3)) hr).elim
    · exact (s16h_false_of_pRank_top_le_one
        (s16h_pRank_le_one_of_isAlt_five_or_isL3_one hq hq2 (Or.inl hA5)) hr).elim
  · obtain ⟨-, -, hs1, -, -⟩ := h6
    exact absurd hs1 (by omega)
  · obtain ⟨-, hL3, -, -⟩ := h7
    exact (s16h_false_of_pRank_top_le_one
      (s16h_pRank_le_one_of_isAlt_five_or_isL3_one hq hq2 (Or.inr hL3)) hr).elim
  · obtain ⟨-, -, hs1, -⟩ := h8
    exact absurd hs1 (by omega)
  · obtain ⟨hcyc, -⟩ := h9
    exact (s16h_false_of_isCyclicOrd_of_quasisimple hcomp.2.2 hcyc).elim
  · obtain ⟨hE, -⟩ := h10
    exact (s16h_false_of_isElemAbelianOfRank_of_quasisimple hcomp.2.2 hE).elim
  · obtain ⟨r, hE, -⟩ := h11
    exact (s16h_false_of_isElemAbelianOfRank_of_quasisimple hcomp.2.2 hE).elim
  · obtain ⟨hcyc, -⟩ := h12
    exact (s16h_false_of_isCyclicOrd_of_quasisimple hcomp.2.2 hcyc).elim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
