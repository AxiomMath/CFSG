module

public import CFSG.ClassicalGroups.Unitary.Finite

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.BorelTits

theorem charP_two_of_card_eq_two_pow {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) : CharP F 2 := by
  have := Fintype.ofFinite F
  exact charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hF])

private lemma two_lt_two_pow {n : ℕ} (hn : 1 < n) : 2 < 2 ^ n :=
  lt_of_le_of_lt (show 2 ≤ n by omega) Nat.lt_two_pow_self

theorem exists_zech_of_card_two_pow {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n) :
    ∃ c : F, c ≠ 0 ∧ c ≠ 1 ∧ ∃ m j : ℕ, c ^ (2 * m) = c ∧ c ^ j = c + 1 := by
  haveI : CharP F 2 := charP_two_of_card_eq_two_pow hF
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hcard : Fintype.card F = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card]; exact hF
  have hord : orderOf g = 2 ^ n - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hF]
  have hcne1 : (g : F) ≠ 1 := by
    intro h
    have h1 : orderOf g = 1 := by rw [Units.ext (v := 1) h, orderOf_one]
    rw [hord] at h1
    have := two_lt_two_pow hn
    omega
  have hcadd : (g : F) + 1 ≠ 0 := fun h => hcne1 (CharTwo.add_eq_zero.mp h)
  obtain ⟨j, hj⟩ : ∃ j : ℕ, (g : F) ^ j = (g : F) + 1 := by
    obtain ⟨j, hj⟩ : Units.mk0 ((g : F) + 1) hcadd ∈ Submonoid.powers g := by
      rw [mem_powers_iff_mem_zpowers]
      exact hg _
    exact ⟨j, by
      rw [← Units.val_pow_eq_pow_val]
      exact (congrArg Units.val hj).trans (Units.val_mk0 hcadd)⟩
  refine ⟨(g : F), g.ne_zero, hcne1, 2 ^ (n - 1), j, ?_, hj⟩
  rw [Nat.mul_comm, Nat.two_pow_pred_mul_two (by omega), ← hcard]
  exact FiniteField.pow_card (g : F)

theorem exists_zech_unitary {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 < n) :
    ∃ c : F, unitaryInvolution F 2 n c = c ∧ c ≠ 0 ∧ c ≠ 1 ∧
      ∃ m j : ℕ, c ^ (2 * m) = c ∧ c ^ j = c + 1 := by
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord : orderOf g = (2 ^ n) ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg,
      CFSG.ClassicalGroups.Unitary.card_units_of_card hF]
  have hq1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  set c : F := unitaryInvolution F 2 n (g : F) * (g : F) with hc
  have hfix : unitaryInvolution F 2 n c = c := by
    rw [hc, map_mul, unitaryInvolution_involutive hF]
    exact mul_comm _ _
  have hcne0 : c ≠ 0 := by
    rw [hc]
    refine mul_ne_zero ?_ g.ne_zero
    rw [unitaryInvolution_apply]
    exact pow_ne_zero _ g.ne_zero
  have hcne1 : c ≠ 1 := by
    rw [hc]
    intro h
    have hpow : g ^ (2 ^ n + 1) = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one, pow_succ, ← unitaryInvolution_apply]
      exact h
    have hdvd := orderOf_dvd_of_pow_eq_one hpow
    rw [hord, CFSG.ClassicalGroups.Unitary.sq_sub_one_eq (2 ^ n) hq1] at hdvd
    have hle : (2 ^ n + 1) * (2 ^ n - 1) ≤ (2 ^ n + 1) * 1 := by
      simpa using Nat.le_of_dvd (by positivity) hdvd
    have hcancel : 2 ^ n - 1 ≤ 1 := Nat.le_of_mul_le_mul_left hle (by positivity)
    have := two_lt_two_pow hn
    omega
  have hpow_card : c ^ (2 ^ n) = c := by
    rw [← unitaryInvolution_apply]
    exact hfix
  have hdfix : unitaryInvolution F 2 n (c + 1) = c + 1 := by
    rw [map_add, map_one, hfix]
  have hd0 : c + 1 ≠ 0 := fun h => hcne1 (CharTwo.add_eq_zero.mp h)
  obtain ⟨x, hx⟩ := CFSG.ClassicalGroups.Unitary.exists_norm_eq_of_fixed hF hdfix hd0
  have hx0 : x ≠ 0 := by
    intro hxzero
    rw [hxzero, map_zero, zero_mul] at hx
    exact hd0 hx.symm
  obtain ⟨i, hi⟩ : ∃ i : ℕ, x = (g : F) ^ i := by
    obtain ⟨i, hi⟩ : Units.mk0 x hx0 ∈ Submonoid.powers g := by
      rw [mem_powers_iff_mem_zpowers]
      exact hg _
    exact ⟨i, by rw [← Units.val_mk0 hx0, ← hi, Units.val_pow_eq_pow_val]⟩
  have hci : c ^ i = c + 1 := by
    have h1 : c ^ i = unitaryInvolution F 2 n x * x := by
      rw [hc, mul_pow, hi, map_pow]
    rw [h1, hx]
  exact ⟨c, hfix, hcne0, hcne1, 2 ^ (n - 1), i,
    by rw [Nat.mul_comm, Nat.two_pow_pred_mul_two (by omega), hpow_card], hci⟩

end CFSG.LocalAnalysis.WeakClosure81

end
