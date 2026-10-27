module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item219LieProof

theorem two_pow_mod_three {n : ℕ} (hn : Even n) : 2 ^ n % 3 = 1 := by
  obtain ⟨r, hr⟩ := hn
  rw [hr, ← two_mul, pow_mul, Nat.pow_mod]
  norm_num

theorem padicValNat_three_eq_one {x : ℕ} (hx : x % 9 = 3 ∨ x % 9 = 6) : padicValNat 3 x = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have h1 : 3 ^ 1 ∣ x := by
    rw [pow_one]
    omega
  have h2 : ¬ 3 ^ 2 ∣ x := by
    norm_num
    omega
  rw [padicValNat_dvd_iff_le hx0] at h1 h2
  omega

theorem residues_mod_nine {q : ℕ} (hq : q % 3 = 1) :
    (q ^ 2 + q + 1) % 9 = 3 ∧ (q ^ 5 + q ^ 4 + q ^ 3 + q ^ 2 + q + 1) % 9 = 6 ∧
      (q ^ 8 + q ^ 4 + 1) % 9 = 3 := by
  have hm : q % 9 ≡ q [MOD 9] := Nat.mod_modEq q 9
  have key : ∀ r : ℕ, r < 9 → r % 3 = 1 → (r ^ 2 + r + 1) % 9 = 3 ∧
      (r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + r + 1) % 9 = 6 ∧ (r ^ 8 + r ^ 4 + 1) % 9 = 3 := by
    decide
  obtain ⟨k1, k2, k3⟩ := key (q % 9) (Nat.mod_lt _ (by norm_num)) (by omega)
  refine ⟨?_, ?_, ?_⟩
  · have h : (q % 9) ^ 2 + q % 9 + 1 ≡ q ^ 2 + q + 1 [MOD 9] := ((hm.pow 2).add hm).add_right 1
    rw [← k1]
    exact h.symm
  · have h : (q % 9) ^ 5 + (q % 9) ^ 4 + (q % 9) ^ 3 + (q % 9) ^ 2 + q % 9 + 1 ≡
        q ^ 5 + q ^ 4 + q ^ 3 + q ^ 2 + q + 1 [MOD 9] :=
      (((((hm.pow 5).add (hm.pow 4)).add (hm.pow 3)).add (hm.pow 2)).add hm).add_right 1
    rw [← k2]
    exact h.symm
  · have h : (q % 9) ^ 8 + (q % 9) ^ 4 + 1 ≡ q ^ 8 + q ^ 4 + 1 [MOD 9] :=
      ((hm.pow 8).add (hm.pow 4)).add_right 1
    rw [← k3]
    exact h.symm

theorem padicValNat_sq_add {q : ℕ} (hq : q % 3 = 1) : padicValNat 3 (q ^ 2 + q + 1) = 1 :=
  padicValNat_three_eq_one (Or.inl (residues_mod_nine hq).1)

theorem padicValNat_torus {q : ℕ} (hq : q % 3 = 1) (hq1 : 1 < q) :
    padicValNat 3 ((q ^ 3 - 1) * (q - 1)) = 2 * padicValNat 3 (q - 1) + 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq0 : q - 1 ≠ 0 := by omega
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
  have e : (p + 1) ^ 3 - 1 = p * ((p + 1) ^ 2 + (p + 1) + 1) := by
    rw [Nat.sub_eq_iff_eq_add (Nat.one_le_pow _ _ (by omega))]
    ring
  rw [e, Nat.add_sub_cancel, padicValNat.mul (by simpa using hq0) (by positivity),
    padicValNat.mul (by simpa using hq0) (by positivity), padicValNat_sq_add hq]
  ring

theorem padicValNat_trialityD4 {q : ℕ} (hq : q % 3 = 1) (hq1 : 1 < q) :
    padicValNat 3 (q ^ 12 * (q ^ 2 - 1) * (q ^ 6 - 1) * (q ^ 8 + q ^ 4 + 1)) =
      2 * padicValNat 3 (q - 1) + 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, k2, k3⟩ := residues_mod_nine hq
  have hq0 : q - 1 ≠ 0 := by omega
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
  have e2 : (p + 1) ^ 2 - 1 = p * (p + 2) := by
    rw [Nat.sub_eq_iff_eq_add (Nat.one_le_pow _ _ (by omega))]
    ring
  have e6 : (p + 1) ^ 6 - 1 = p * ((p + 1) ^ 5 + (p + 1) ^ 4 + (p + 1) ^ 3 + (p + 1) ^ 2 +
      (p + 1) + 1) := by
    rw [Nat.sub_eq_iff_eq_add (Nat.one_le_pow _ _ (by omega))]
    ring
  rw [Nat.add_sub_cancel] at hq0
  have hp0 : p ≠ 0 := hq0
  have h12 : padicValNat 3 ((p + 1) ^ 12) = 0 := by
    refine padicValNat.eq_zero_of_not_dvd fun h => ?_
    have := Nat.prime_three.dvd_of_dvd_pow h
    omega
  have hp2 : padicValNat 3 (p + 2) = 0 := padicValNat.eq_zero_of_not_dvd (by omega)
  rw [e2, e6, Nat.add_sub_cancel, padicValNat.mul (by positivity) (by positivity),
    padicValNat.mul (by positivity) (by positivity), padicValNat.mul (by positivity)
      (by positivity), padicValNat.mul hp0 (by positivity), padicValNat.mul hp0 (by positivity),
    h12, hp2, padicValNat_three_eq_one (Or.inr k2), padicValNat_three_eq_one (Or.inl k3)]
  ring

theorem pow_three_eq_one_of_pow_sq_add {G : Type*} [Monoid G] {q : ℕ} (hq : q % 3 = 1) {a : G}
    {m : ℕ} (ham : a ^ 3 ^ m = 1) (haq : a ^ (q ^ 2 + q + 1) = 1) : a ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨j, hj, hord⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one ham)
  have hdvd : 3 ^ j ∣ q ^ 2 + q + 1 := hord ▸ orderOf_dvd_of_pow_eq_one haq
  have hj1 : j ≤ 1 := by
    have h := (padicValNat_dvd_iff_le (p := 3) (by positivity)).mp hdvd
    rwa [padicValNat_sq_add hq] at h
  rw [← orderOf_dvd_iff_pow_eq_one, hord]
  exact (Nat.pow_dvd_pow 3 hj1).trans (by norm_num)

end CFSG.RankThree.PartTwo.Sec21.Item219LieProof
