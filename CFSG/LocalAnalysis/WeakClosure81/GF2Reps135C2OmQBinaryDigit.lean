module

public import Mathlib.Data.Nat.Choose.Lucas

public section

namespace CFSG.LocalAnalysis.WeakClosure81

theorem omq_exists_odd_choose_lt {c : ℕ} (hc : 1 ≤ c) (hpow : ∀ a : ℕ, c ≠ 2 ^ a) :
    ∃ j : ℕ, 0 < j ∧ j < c ∧ Odd (Nat.choose c j) := by
  revert hc hpow
  refine Nat.strong_induction_on c ?_
  intro n ih hc hpow
  rcases Nat.even_or_odd n with hev | hod
  · obtain ⟨d, rfl⟩ := even_iff_exists_two_mul.mp hev
    have hd_pos : 1 ≤ d := by omega
    have hd_notpow : ∀ a : ℕ, d ≠ 2 ^ a := by
      intro a hda
      exact hpow (a + 1) (by rw [hda, pow_succ]; ring)
    have hd_lt : d < 2 * d := by omega
    obtain ⟨j', hj'pos, hj'lt, hj'odd⟩ := ih d hd_lt hd_pos hd_notpow
    refine ⟨2 * j', by omega, by omega, ?_⟩
    have hmod : Nat.choose (2 * d) (2 * j') ≡ Nat.choose d j' [MOD 2] :=
      Choose.choose_mul_mul_modEq_choose_nat (p := 2) (a := d) (b := j')
    have hmod1 : Nat.choose d j' ≡ 1 [MOD 2] := by
      simp [Nat.ModEq, Nat.odd_iff.mp hj'odd]
    exact Nat.odd_iff.mpr (by simpa [Nat.ModEq] using hmod.trans hmod1)
  · have hc_ne_one : n ≠ 1 := by
      intro h
      exact hpow 0 (by rw [h, pow_zero])
    refine ⟨1, by norm_num, by omega, ?_⟩
    simpa [Nat.choose_one_right] using hod

end CFSG.LocalAnalysis.WeakClosure81
