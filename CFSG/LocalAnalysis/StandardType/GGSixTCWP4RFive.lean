module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RFlag

public section

namespace CFSG.StandardType.TableCRes


open Certificates.TcRes

section FlagFive

theorem tc_two_pow_mod_five (n : ℕ) :
    2 ^ n % 5 = if n % 4 = 0 then 1 else if n % 4 = 1 then 2 else if n % 4 = 2 then 4 else 3 := by
  have h : 2 ^ n = 16 ^ (n / 4) * 2 ^ (n % 4) := by
    rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul, ← pow_add, Nat.div_add_mod]
  rw [h, Nat.mul_mod, Nat.pow_mod]
  have h16 : (16 : ℕ) % 5 = 1 := by norm_num
  rw [h16, one_pow]
  have hn : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases hm : n % 4 <;> simp

theorem tc_five_dvd_two_pow_sub_one_iff (n : ℕ) : ((2 ^ n - 1) % 5 == 0) = (n % 4 == 0) := by
  have h := tc_two_pow_mod_five n
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq]
  split_ifs at h <;> omega

private theorem tc_five_dvd_two_pow_add_one_iff (n : ℕ) :
    ((2 ^ n + 1) % 5 == 0) = (n % 4 == 2) := by
  have h := tc_two_pow_mod_five n
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq]
  split_ifs at h <;> omega

private theorem tc_splitT_five_congr {t : TcrTg} {r n n' : ℕ} (h : n % 4 = n' % 4) :
    tcrSplitT 5 ⟨t, r, n⟩ = tcrSplitT 5 ⟨t, r, n'⟩ := by
  have ha : ((2 ^ n - 1) % 5 == 0) = ((2 ^ n' - 1) % 5 == 0) := by
    rw [tc_five_dvd_two_pow_sub_one_iff, tc_five_dvd_two_pow_sub_one_iff, h]
  have hb : ((2 ^ n + 1) % 5 == 0) = ((2 ^ n' + 1) % 5 == 0) := by
    rw [tc_five_dvd_two_pow_add_one_iff, tc_five_dvd_two_pow_add_one_iff, h]
  simp only [tcrSplitT, ha, hb, Nat.reduceBEq, Bool.and_false, Bool.or_false]

private theorem tc_halfSplitT_five_congr {t : TcrTg} {r n n' : ℕ} (h : n % 4 = n' % 4)
    (h2 : (n == 2) = (n' == 2)) :
    tcrHalfSplitT 5 ⟨t, r, n⟩ = tcrHalfSplitT 5 ⟨t, r, n'⟩ := by
  have ha : ((2 ^ n - 1) % 5 == 0) = ((2 ^ n' - 1) % 5 == 0) := by
    rw [tc_five_dvd_two_pow_sub_one_iff, tc_five_dvd_two_pow_sub_one_iff, h]
  have hb : ((2 ^ n + 1) % 5 == 0) = ((2 ^ n' + 1) % 5 == 0) := by
    rw [tc_five_dvd_two_pow_add_one_iff, tc_five_dvd_two_pow_add_one_iff, h]
  simp only [tcrHalfSplitT, tc_splitT_five_congr h, ha, hb, h2, Nat.reduceBEq, Bool.and_false,
    Bool.or_false, Bool.and_true]

theorem flagTransfer_five {F F' : ℕ} (hF : F % 2 = 1) (hF' : F' % 2 = 1) (h4 : F % 4 = F' % 4)
    (h3 : 3 ≤ F) (h3' : 3 ≤ F') : FlagTransfer 5 F F' := by
  have hmod : ∀ n : ℕ, n * F % 4 = n * F' % 4 := fun n => by
    rw [Nat.mul_mod, h4, ← Nat.mul_mod]
  have hne : ∀ (n G : ℕ), 3 ≤ G → (n * G == 2) = false := fun n G hG => by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp
    · have : G ≤ n * G := Nat.le_mul_of_pos_left G hn
      have h2 : n * G ≠ 2 := by omega
      simpa using h2
  have hsplit : ∀ l : TcrLab, tcrSplitT 5 (flagScaleLab F l) = tcrSplitT 5 (flagScaleLab F' l) := by
    rintro ⟨t, r, n⟩
    exact tc_splitT_five_congr (hmod n)
  have hhalf : ∀ l : TcrLab,
      tcrHalfSplitT 5 (flagScaleLab F l) = tcrHalfSplitT 5 (flagScaleLab F' l) := by
    rintro ⟨t, r, n⟩
    exact tc_halfSplitT_five_congr (hmod n) (by rw [hne n F h3, hne n F' h3'])
  intro d
  refine ⟨?_, ?_, ?_⟩
  · intro h
    simp only [flagLabsOf_scale hF, flagLabsOf_scale hF', List.any_map, Function.comp_def,
      hsplit] at h ⊢
    exact h
  · intro h
    simp only [flagLabsOf_scale hF, flagLabsOf_scale hF', List.any_map, Function.comp_def,
      hhalf] at h ⊢
    exact h
  · intro d2 h
    simp only [flagLabsOf_scale hF, flagLabsOf_scale hF', flagAnyContains hF,
      flagAnyContains hF'] at h ⊢
    exact h

end FlagFive

end CFSG.StandardType.TableCRes

end
