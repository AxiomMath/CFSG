module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSmallShapes
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsNineAdjRoot
import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
import CFSG.RankThree.GF2n.Stroth80.Sec4Classical

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {Y : Type} [Group Y] [Finite Y]

private theorem w183_two_le_of_isSpn {X : Type} [Group X] {n a : ℕ}
    (hq : CFSG.Open.IsQuasisimple X) (hshape : IsSpn X n a) : 2 ≤ n := by
  by_contra hlt
  obtain ⟨hev, K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hshape
  let := hKf
  have hn0 : n = 0 := by
    obtain ⟨k, hk⟩ := hev
    omega
  rw [hn0] at e
  have hdiv : (0 : ℕ) / 2 = 0 := by norm_num
  rw [hdiv] at e
  have : Subsingleton ↥(StatedSp 0 K) :=
    ⟨fun x y => Subtype.ext (Units.ext (Matrix.ext fun i => isEmptyElim i))⟩
  have : Subsingleton X :=
    ⟨fun x y => e.injective (Subsingleton.elim _ _)⟩
  have : Nontrivial (X ⧸ Subgroup.center X) := hq.2.toNontrivial
  have : Nontrivial X := (QuotientGroup.mk'_surjective (Subgroup.center X)).nontrivial
  exact (not_subsingleton_iff_nontrivial (α := X)).mpr inferInstance inferInstance

private theorem w183_pRank_le_one_of_isSpn_two {X : Type} [Group X] [Finite X] {a : ℕ}
    (ha : 2 ≤ a) (hshape : IsSpn X 2 a)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    CFSG.Open.pRank q (⊤ : Subgroup X) ≤ 1 := by
  obtain ⟨-, K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hshape
  let := hKf
  let := hKfin
  obtain ⟨e2⟩ :=
    CFSG.RankThree.GF2n.Stroth80.nonempty_statedSp_one_mulEquiv_statedSL_two K
  have hdiv : (2 : ℕ) / 2 = 1 := by norm_num
  have he : X ≃* ↥(StatedSp 1 K) := by simpa [hdiv] using e
  have hSL : IsSLn X 2 a := ⟨K, hKf, hKfin, hKcard, ⟨he.trans e2⟩⟩
  exact CFSG.LocalAnalysis.UniquenessCase.UC22.pRank_le_one_of_isL2_or_isSz
    (Or.inl (CFSG.GroupTheory.isL2_of_isSLn_two ha hSL)) hq hq2

theorem s16nt_range_sp {n a : ℕ} (hq : CFSG.Open.IsQuasisimple Y)
    (hnt : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ 2 ≤ CFSG.Open.pRank q (⊤ : Subgroup Y))
    (h : IsSpn Y n a) : 6 ≤ n ∨ (n = 4 ∧ 2 ≤ a) := by
  have hev : Even n := h.1
  have ha1 : 1 ≤ a := by
    obtain ⟨-, K, hKf, hKfin, hKcard, -⟩ := h
    let := hKf
    haveI : Nontrivial K := inferInstance
    have hlt : 1 < Nat.card K := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
    rw [hKcard] at hlt
    have hpow : 2 ^ 1 ≤ 2 ^ a := by
      have : 2 ≤ 2 ^ a := Nat.succ_le_iff.mpr hlt
      simpa using this
    exact (Nat.pow_le_pow_iff_right (by norm_num : (1 : ℕ) < 2)).mp hpow
  have hle4 : 4 ≤ n := by
    by_cases haeq : a = 1
    · have h6 : 6 ≤ n := s16k_six_le_of_isSpn hq (by rwa [haeq] at h)
      omega
    · by_contra h4
      have hn : n = 0 ∨ n = 2 := by
        obtain ⟨k, hk⟩ := hev
        omega
      rcases hn with hn0 | hn2
      · have := w183_two_le_of_isSpn hq h
        omega
      · have h2 : IsSpn Y 2 a := by rw [hn2] at h; exact h
        have ha2 : 2 ≤ a := by omega
        obtain ⟨q, hqp, hq2, hqrank⟩ := hnt
        have hle := w183_pRank_le_one_of_isSpn_two ha2 h2 hqp hq2
        omega
  by_cases h6 : 6 ≤ n
  · exact Or.inl h6
  · right
    refine ⟨?_, ?_⟩
    · obtain ⟨k, hk⟩ := hev
      omega
    · by_contra ha2
      have haeq : a = 1 := by omega
      have h6' : 6 ≤ n := s16k_six_le_of_isSpn hq (by rwa [haeq] at h)
      exact absurd h6' h6

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
