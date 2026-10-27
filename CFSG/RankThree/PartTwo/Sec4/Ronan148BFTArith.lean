module

public import CFSG.RankThree.PartTwo.KFacts.AutPSLOrderThree

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148B

open CFSG.LocalAnalysis.ComponentInitial

theorem exists_prime_dvd_cube_add_one {n : ℕ} (hn : Odd n) (hn3 : 3 ≤ n) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 3 ∧ r ∣ (2 ^ n) ^ 3 + 1 ∧ ¬ r ∣ (2 ^ n) ^ 2 - 1 ∧
      ¬ r ∣ (2 ^ n) ^ 4 - 1 := by
  set q := 2 ^ n with hq
  have hq3 : q % 3 = 2 := by
    obtain ⟨k, rfl⟩ := hn
    rw [hq, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hq8 : 8 ≤ q := by
    rw [hq]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
  obtain ⟨t, ht⟩ : ∃ t, q = 3 * t + 2 := ⟨q / 3, by omega⟩
  have ht2 : 2 ≤ t := by omega
  set m := 3 * t ^ 2 + 3 * t + 1 with hm
  have hm1 : m ≠ 1 := by
    have : 1 < m := by nlinarith
    omega
  have hm3 : ¬ 3 ∣ m := by omega
  have hm2 : ¬ 2 ∣ m := by
    rintro ⟨k, hk⟩
    have : (t * (t + 1)) % 2 = 0 := by
      rcases Nat.even_or_odd t with ⟨a, rfl⟩ | ⟨a, rfl⟩
      · rw [show (a + a) * (a + a + 1) = 2 * (a * (2 * a + 1)) by ring]; simp
      · rw [show (2 * a + 1) * (2 * a + 1 + 1) = 2 * ((2 * a + 1) * (a + 1)) by ring]; simp
    have e : m = 3 * (t * (t + 1)) + 1 := by rw [hm]; ring
    omega
  have hsq : q ^ 2 + 1 = 3 * m + q := by rw [ht, hm]; ring
  have hcube : q ^ 3 + 1 = 3 * (q + 1) * m := by rw [ht, hm]; ring
  set r := m.minFac with hr
  have hrp : r.Prime := Nat.minFac_prime hm1
  have hrm : r ∣ m := Nat.minFac_dvd m
  have hr3 : r ≠ 3 := fun h => hm3 (h ▸ hrm)
  have hr2 : r ≠ 2 := fun h => hm2 (h ▸ hrm)
  haveI : Fact r.Prime := ⟨hrp⟩
  have hm0 : ((m : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hrm
  have hsqz : ((q : ℕ) : ZMod r) ^ 2 + 1 = (q : ZMod r) := by
    have := congrArg (fun x : ℕ => (x : ZMod r)) hsq
    simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_mul, Nat.cast_one] at this
    rw [this, hm0, mul_zero, zero_add]
  have hno1 : ((q : ℕ) : ZMod r) ^ 2 ≠ 1 := by
    intro h1
    have hq2 : ((q : ℕ) : ZMod r) = 2 := by
      rw [← hsqz, h1]
      norm_num
    have h3' : (3 : ZMod r) = 0 := by
      rw [hq2] at h1
      linear_combination h1
    have h3 : ((3 : ℕ) : ZMod r) = 0 := by exact_mod_cast h3'
    exact hr3 ((Nat.prime_dvd_prime_iff_eq hrp Nat.prime_three).mp
      ((ZMod.natCast_eq_zero_iff _ _).mp h3))
  refine ⟨r, hrp, hr3, ?_, ?_, ?_⟩
  · rw [hcube]
    exact Dvd.dvd.mul_left hrm _
  · intro hd
    apply hno1
    have h1 : (((q ^ 2 - 1 : ℕ)) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), sub_eq_zero] at h1
    simpa using h1
  · intro hd
    have h1 : (((q ^ 4 - 1 : ℕ)) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), sub_eq_zero] at h1
    push_cast at h1
    have hfac : (((q : ℕ) : ZMod r) ^ 2 - 1) * (((q : ℕ) : ZMod r) ^ 2 + 1) = 0 := by
      rw [← sub_eq_zero.mpr h1]; ring
    rcases mul_eq_zero.mp hfac with h | h
    · exact hno1 (sub_eq_zero.mp h)
    ·
      rw [hsqz] at h
      have h2 : r ∣ q := (ZMod.natCast_eq_zero_iff _ _).mp h
      rw [hq] at h2
      exact hr2 ((Nat.prime_dvd_prime_iff_eq hrp Nat.prime_two).mp
        (hrp.dvd_of_dvd_pow h2))

theorem pow_eq_self_of_pow_three {M : Type*} [Monoid M] {x : M} (hx : x ^ 3 = 1) {k : ℕ}
    (hk : k % 3 = 1) : x ^ k = x := by
  rw [← Nat.mod_add_div k 3, pow_add, pow_mul, hx, one_pow, mul_one, hk, pow_one]

theorem fieldAut_three_facts {n : ℕ} (hn : 1 ≤ n) {F : Type} [Field F]
    (hF : Nat.card F = 2 ^ (2 * (3 * n))) {τ : F ≃+* F} (hτ : orderOf τ = 3) :
    (∀ x, τ (τ (τ x)) = x) ∧ (∀ x : F, x ^ 3 = 1 → τ x = x) ∧
      (∀ x : F, τ x = x → x ^ ((2 ^ n) ^ 2) = x ∨ x ^ ((2 ^ n) ^ 4) = x) := by
  obtain ⟨-, hτform⟩ := CFSG.RankThree.PartTwo.KFacts.eq_frobenius_pow_of_orderOf_eq_three
    Nat.prime_two (by omega : 1 ≤ 2 * (3 * n)) hF hτ
  have e1 : 2 * (3 * n) / 3 = 2 * n := by omega
  have e2 : 2 * (2 * (3 * n)) / 3 = 4 * n := by omega
  rw [e1, e2] at hτform
  have hp2 : (2 ^ n) ^ 2 = 2 ^ (2 * n) := by rw [← pow_mul, mul_comm]
  have hp4 : (2 ^ n) ^ 4 = 2 ^ (4 * n) := by rw [← pow_mul, mul_comm]
  refine ⟨fun x => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · have h3 : τ ^ 3 = 1 := by rw [← hτ]; exact pow_orderOf_eq_one τ
    have := congrArg (fun σ : F ≃+* F => σ x) h3
    simpa [pow_succ, RingAut.mul_apply] using this
  · rcases hτform with h | h
    · rw [h]
      exact pow_eq_self_of_pow_three hx (by rw [pow_mul, Nat.pow_mod]; norm_num)
    · rw [h]
      exact pow_eq_self_of_pow_three hx (by rw [pow_mul, Nat.pow_mod]; norm_num)
  · rcases hτform with h | h
    · left
      rw [hp2, ← h x, hx]
    · right
      rw [hp4, ← h x, hx]

end CFSG.RankThree.PartTwo.Sec4.Ronan148B
