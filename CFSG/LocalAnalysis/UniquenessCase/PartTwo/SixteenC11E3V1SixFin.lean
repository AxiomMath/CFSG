module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1SixFinB
public import CFSG.Quasithin.Background.E3Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

private theorem s1611e3_mQuot_lt_two_of_card {G : Type*} [Group G] [Finite G]
    {E B : Subgroup G} (hB : B ≤ E) (hcard : Nat.card E = 2 * Nat.card B) :
    E3.mQuot E B < 2 := by
  have h1 := Subgroup.relIndex_mul_card B E
  rw [inf_eq_left.2 hB] at h1
  have hpos : 0 < Nat.card B := Nat.card_pos
  have h2 : B.relIndex E = 2 := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [h1, hcard]
  unfold E3.mQuot
  rw [h2, padicValNat_self (p := 2)]
  norm_num

theorem s1611e3_six_finite_check {K : Subgroup (SixE6 × SixE6)} (hK : K = ⊥ ∨ K = sixDiag)
    {E : Subgroup (MulAut (SixE6 × SixE6))} (hEG : E ≤ sixGhat) (hE1 : E ≠ ⊥)
    (hEab : IsElemAbelian2 (V := SixE6 × SixE6) E) :
    ∃ B : Subgroup (MulAut (SixE6 × SixE6)), B ≤ E ∧ E3.mQuot E B < 2 ∧
      sixFixMod K B ≠ sixFixMod K E := by
  obtain ⟨h2, h4, h8, hle⟩ := sixFinCheck_of hK
  haveI : Finite ↥E := inferInstance
  obtain ⟨n, hn⟩ := hEab.isPGroup.exists_card_eq
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      have hc : Nat.card ↥E = 1 := by rw [hn, h]; norm_num
      exact hE1 ((Subgroup.eq_bot_iff_card E).mpr hc)
    · exact h
  have hn3 : n ≤ 3 := by
    have hle8 : 2 ^ n ≤ 8 := by rw [← hn]; exact hle E hEG hEab
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < (2 : ℕ))).1 (by simpa using hle8)
  have hcases : n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases hcases with hn_eq | hn_eq | hn_eq
  · subst hn_eq
    have hc : Nat.card ↥E = 2 := by rw [hn]; norm_num
    refine ⟨⊥, bot_le, ?_, h2 E hEG hEab hc⟩
    have hcard : Nat.card ↥E =
        2 * Nat.card ↥(⊥ : Subgroup (MulAut (SixE6 × SixE6))) := by
      simp [hc, Subgroup.card_bot]
    exact s1611e3_mQuot_lt_two_of_card bot_le hcard
  · subst hn_eq
    have hc : Nat.card ↥E = 4 := by rw [hn]; norm_num
    obtain ⟨B, hBE, hBcard, hfix⟩ := h4 E hEG hEab hc
    refine ⟨B, hBE, ?_, hfix⟩
    have hcard : Nat.card ↥E = 2 * Nat.card ↥B := by simp [hc, hBcard]
    exact s1611e3_mQuot_lt_two_of_card hBE hcard
  · subst hn_eq
    have hc : Nat.card ↥E = 8 := by rw [hn]; norm_num
    obtain ⟨B, hBE, hBcard, hfix⟩ := h8 E hEG hEab hc
    refine ⟨B, hBE, ?_, hfix⟩
    have hcard : Nat.card ↥E = 2 * Nat.card ↥B := by simp [hc, hBcard]
    exact s1611e3_mQuot_lt_two_of_card hBE hcard

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
