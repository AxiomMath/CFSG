module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailCountComparison

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

theorem tailCount_three_two_one_lt_three (q : ℕ) (hq : 2 ≤ q) :
    tailCount (q : ℚ) 3 2 1 < tailCount (q : ℚ) 3 2 3 := by
  have hq' : (2 : ℚ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℚ) < q := by linarith
  have hq1 : (1 : ℚ) ≤ q := by linarith
  have hden2 : (q : ℚ) ^ 2 - 1 ≠ 0 :=
    (pow_sub_one_pos_of_two_le hq' (m := 2) (by norm_num)).ne'
  have hden3 : (q : ℚ) ^ 3 - 1 ≠ 0 :=
    (pow_sub_one_pos_of_two_le hq' (m := 3) (by norm_num)).ne'
  have hdenq : (0 : ℚ) < (q : ℚ) ^ 2 + (q : ℚ) + 1 := by positivity
  have hC2 : tailCount (q : ℚ) 3 2 2 =
      tailCount (q : ℚ) 3 2 1 * ((q : ℚ) ^ 3 + 1) := by
    have h : tailCount (q : ℚ) 3 2 2 =
        tailCount (q : ℚ) 3 2 1 *
          (((q : ℚ) ^ 2 - 1) * ((q : ℚ) ^ 3 + 1) / ((q : ℚ) ^ 2 - 1)) := by
      simpa using tailCount_succ (q := (q : ℚ)) 3 2 1
    rw [h, mul_div_cancel_left₀ ((q : ℚ) ^ 3 + 1) hden2]
  have hC3 : tailCount (q : ℚ) 3 2 3 =
      tailCount (q : ℚ) 3 2 2 *
        (((q : ℚ) - 1) * ((q : ℚ) ^ 2 + 1) / ((q : ℚ) ^ 3 - 1)) := by
    simpa using tailCount_succ (q := (q : ℚ)) 3 2 2
  have hC3' : tailCount (q : ℚ) 3 2 3 =
      tailCount (q : ℚ) 3 2 1 * ((q : ℚ) ^ 3 + 1) *
        (((q : ℚ) ^ 2 + 1) / ((q : ℚ) ^ 2 + (q : ℚ) + 1)) := by
    rw [hC3, hC2]
    congr 1
    rw [div_eq_div_iff hden3 hdenq.ne']
    ring
  rw [hC3']
  have hA : 1 < ((q : ℚ) ^ 3 + 1) *
      (((q : ℚ) ^ 2 + 1) / ((q : ℚ) ^ 2 + (q : ℚ) + 1)) := by
    rw [← mul_div_assoc, one_lt_div hdenq]
    have hfac : ((q : ℚ) ^ 3 + 1) * ((q : ℚ) ^ 2 + 1) =
        ((q : ℚ) ^ 2 + (q : ℚ) + 1) + (q : ℚ) * ((q : ℚ) ^ 4 + (q : ℚ) ^ 2 - 1) := by
      ring
    have h4 : (1 : ℚ) ≤ (q : ℚ) ^ 4 := one_le_pow₀ hq1
    have h2 : (1 : ℚ) ≤ (q : ℚ) ^ 2 := one_le_pow₀ hq1
    have hp : 0 < (q : ℚ) * ((q : ℚ) ^ 4 + (q : ℚ) ^ 2 - 1) := by
      have : 0 < (q : ℚ) ^ 4 + (q : ℚ) ^ 2 - 1 := by linarith
      exact mul_pos hq0 this
    linarith
  have hpos : 0 < tailCount (q : ℚ) 3 2 1 :=
    tailCount_pos hq' (r := 3) (m := 2) (k := 1) (by norm_num)
  calc tailCount (q : ℚ) 3 2 1 = tailCount (q : ℚ) 3 2 1 * 1 := (mul_one _).symm
    _ < tailCount (q : ℚ) 3 2 1 *
          (((q : ℚ) ^ 3 + 1) *
            (((q : ℚ) ^ 2 + 1) / ((q : ℚ) ^ 2 + (q : ℚ) + 1))) :=
        mul_lt_mul_of_pos_left hA hpos
    _ = tailCount (q : ℚ) 3 2 1 * ((q : ℚ) ^ 3 + 1) *
          (((q : ℚ) ^ 2 + 1) / ((q : ℚ) ^ 2 + (q : ℚ) + 1)) := by ring

theorem tailCount_three_two_three_lt_two (q : ℕ) (hq : 2 ≤ q) :
    tailCount (q : ℚ) 3 2 3 < tailCount (q : ℚ) 3 2 2 := by
  have hq' : (2 : ℚ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℚ) < q := by linarith
  have hqm1 : (0 : ℚ) < (q : ℚ) - 1 := by linarith
  have hden3 : (0 : ℚ) < (q : ℚ) ^ 3 - 1 :=
    pow_sub_one_pos_of_two_le hq' (m := 3) (by norm_num)
  have hC3 : tailCount (q : ℚ) 3 2 3 =
      tailCount (q : ℚ) 3 2 2 *
        (((q : ℚ) - 1) * ((q : ℚ) ^ 2 + 1) / ((q : ℚ) ^ 3 - 1)) := by
    simpa using tailCount_succ (q := (q : ℚ)) 3 2 2
  have hR : ((q : ℚ) - 1) * ((q : ℚ) ^ 2 + 1) / ((q : ℚ) ^ 3 - 1) < 1 := by
    rw [div_lt_one hden3]
    nlinarith [mul_pos hq0 hqm1]
  have hpos : 0 < tailCount (q : ℚ) 3 2 2 :=
    tailCount_pos hq' (r := 3) (m := 2) (k := 2) (by norm_num)
  calc tailCount (q : ℚ) 3 2 3 =
        tailCount (q : ℚ) 3 2 2 *
          (((q : ℚ) - 1) * ((q : ℚ) ^ 2 + 1) / ((q : ℚ) ^ 3 - 1)) := hC3
    _ < tailCount (q : ℚ) 3 2 2 * 1 := mul_lt_mul_of_pos_left hR hpos
    _ = tailCount (q : ℚ) 3 2 2 := mul_one _

theorem tailCount_three_two_pairwise (q : ℕ) (hq : 2 ≤ q) :
    tailCount (q : ℚ) 3 2 1 ≠ tailCount (q : ℚ) 3 2 2 ∧
      tailCount (q : ℚ) 3 2 1 ≠ tailCount (q : ℚ) 3 2 3 ∧
      tailCount (q : ℚ) 3 2 2 ≠ tailCount (q : ℚ) 3 2 3 := by
  have h13 := tailCount_three_two_one_lt_three q hq
  have h32 := tailCount_three_two_three_lt_two q hq
  exact ⟨(h13.trans h32).ne, h13.ne, h32.ne'⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
