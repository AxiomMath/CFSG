module

public import CFSG.Open.Defs

public section

namespace CFSG.RankThree.PartOne.F106

open CFSG.Open

theorem two_mul_tri (m : ℕ) : 2 * (m * (m + 1) / 2) = m * (m + 1) :=
  Nat.mul_div_cancel' (Nat.even_mul_succ_self m).two_dvd

theorem prod_sub_one_le (Q : ℕ) (s : Finset ℕ) (g : ℕ → ℕ) :
    ∏ i ∈ s, (Q ^ g i - 1) ≤ Q ^ (∑ i ∈ s, g i) := by
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod (fun i _ => Nat.sub_le _ _)

theorem two_mul_sum_Icc_two (m : ℕ) : 2 * ∑ i ∈ Finset.Icc 2 (m + 1), i = m * (m + 3) := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih]
    ring

theorem two_mul_sum_Icc_one (m : ℕ) : ∑ i ∈ Finset.Icc 1 m, 2 * i = m * (m + 1) := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    ring

theorem ordTwistedA_le (m Q : ℕ) (hQ : 2 ≤ Q) : ordTwistedA m Q ≤ Q ^ (m * (m + 2) + m) := by
  unfold ordTwistedA
  refine (Nat.div_le_self _ _).trans ?_
  have hf : ∀ i ∈ Finset.Icc 2 (m + 1),
      (((Q : ℤ) ^ i - (-1) ^ i).toNat) ≤ Q ^ (i + 1) := by
    intro i hi
    have hi2 : 2 ≤ i := (Finset.mem_Icc.mp hi).1
    have h1 : (1 : ℤ) ≤ Q ^ i := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ Q))
    have h2 : ((Q : ℤ) ^ i - (-1) ^ i) ≤ (Q : ℤ) ^ (i + 1) := by
      have h3 : (-1 : ℤ) ^ i ≥ -1 := by
        rcases neg_one_pow_eq_or ℤ i with h | h <;> simp [h]
      have h4 : (Q : ℤ) ^ (i + 1) = Q ^ i * Q := pow_succ _ _
      have h5 : (2 : ℤ) ≤ Q := by exact_mod_cast hQ
      nlinarith
    exact_mod_cast Int.toNat_le_toNat h2 |>.trans (by simp)
  calc Q ^ (m * (m + 1) / 2) * ∏ i ∈ Finset.Icc 2 (m + 1), (((Q : ℤ) ^ i - (-1) ^ i).toNat)
      ≤ Q ^ (m * (m + 1) / 2) * ∏ i ∈ Finset.Icc 2 (m + 1), Q ^ (i + 1) := by
        gcongr with i hi
        exact hf i hi
    _ = Q ^ (m * (m + 1) / 2) * Q ^ (∑ i ∈ Finset.Icc 2 (m + 1), (i + 1)) := by
        rw [Finset.prod_pow_eq_pow_sum]
    _ = Q ^ (m * (m + 2) + m) := by
        rw [← pow_add]
        congr 1
        have h1 := two_mul_tri m
        have h2 := two_mul_sum_Icc_two m
        have h3 : ∑ i ∈ Finset.Icc 2 (m + 1), (i + 1) = ∑ i ∈ Finset.Icc 2 (m + 1), i + m := by
          rw [Finset.sum_add_distrib]
          simp
        have h4 : m * (m + 1) + m * (m + 3) = 2 * (m * (m + 2)) := by ring
        omega

theorem ordA_le (m Q : ℕ) : ordA m Q ≤ Q ^ (m * (m + 2)) := by
  unfold ordA
  refine (Nat.div_le_self _ _).trans ?_
  calc Q ^ (m * (m + 1) / 2) * ∏ i ∈ Finset.Icc 2 (m + 1), (Q ^ i - 1)
      ≤ Q ^ (m * (m + 1) / 2) * Q ^ (∑ i ∈ Finset.Icc 2 (m + 1), i) := by
        gcongr
        simpa using prod_sub_one_le Q (Finset.Icc 2 (m + 1)) (fun i => i)
    _ = Q ^ (m * (m + 2)) := by
        rw [← pow_add]
        congr 1
        have h1 := two_mul_tri m
        have h2 := two_mul_sum_Icc_two m
        have h3 : m * (m + 1) + m * (m + 3) = 2 * (m * (m + 2)) := by ring
        omega

theorem ordBC_le (n Q : ℕ) : ordBC n Q ≤ Q ^ (n * n + n * (n + 1)) := by
  unfold ordBC
  refine (Nat.div_le_self _ _).trans ?_
  rw [pow_add]
  gcongr
  calc ∏ i ∈ Finset.Icc 1 n, (Q ^ (2 * i) - 1) ≤ Q ^ (∑ i ∈ Finset.Icc 1 n, 2 * i) :=
        prod_sub_one_le Q _ (fun i => 2 * i)
    _ = Q ^ (n * (n + 1)) := by rw [two_mul_sum_Icc_one]

theorem ordD_le (k Q : ℕ) :
    ordD (k + 1) Q ≤ Q ^ ((k + 1) * k + (k + 1) + k * (k + 1)) := by
  unfold ordD
  refine (Nat.div_le_self _ _).trans ?_
  rw [show k + 1 - 1 = k from rfl]
  calc Q ^ ((k + 1) * k) * (Q ^ (k + 1) - 1) * ∏ i ∈ Finset.Icc 1 k, (Q ^ (2 * i) - 1)
      ≤ Q ^ ((k + 1) * k) * Q ^ (k + 1) * Q ^ (k * (k + 1)) := by
        gcongr
        · exact Nat.sub_le _ _
        · calc ∏ i ∈ Finset.Icc 1 k, (Q ^ (2 * i) - 1) ≤ Q ^ (∑ i ∈ Finset.Icc 1 k, 2 * i) :=
              prod_sub_one_le Q _ (fun i => 2 * i)
            _ = Q ^ (k * (k + 1)) := by rw [two_mul_sum_Icc_one]
    _ = Q ^ ((k + 1) * k + (k + 1) + k * (k + 1)) := by rw [← pow_add, ← pow_add]

theorem ordTwistedD_le (k Q : ℕ) (hQ : 2 ≤ Q) :
    ordTwistedD (k + 1) Q ≤ Q ^ ((k + 1) * k + (k + 1 + 1) + k * (k + 1)) := by
  unfold ordTwistedD
  refine (Nat.div_le_self _ _).trans ?_
  rw [show k + 1 - 1 = k from rfl]
  have h1 : Q ^ (k + 1) + 1 ≤ Q ^ (k + 1 + 1) := by
    have : 1 ≤ Q ^ (k + 1) := Nat.one_le_pow _ _ (by omega)
    calc Q ^ (k + 1) + 1 ≤ Q ^ (k + 1) * Q := by nlinarith
      _ = Q ^ (k + 1 + 1) := (pow_succ _ _).symm
  calc Q ^ ((k + 1) * k) * (Q ^ (k + 1) + 1) * ∏ i ∈ Finset.Icc 1 k, (Q ^ (2 * i) - 1)
      ≤ Q ^ ((k + 1) * k) * Q ^ (k + 1 + 1) * Q ^ (k * (k + 1)) := by
        gcongr
        calc ∏ i ∈ Finset.Icc 1 k, (Q ^ (2 * i) - 1) ≤ Q ^ (∑ i ∈ Finset.Icc 1 k, 2 * i) :=
              prod_sub_one_le Q _ (fun i => 2 * i)
            _ = Q ^ (k * (k + 1)) := by rw [two_mul_sum_Icc_one]
    _ = Q ^ ((k + 1) * k + (k + 1 + 1) + k * (k + 1)) := by rw [← pow_add, ← pow_add]

theorem ordF4_le (Q : ℕ) : ordF4 Q ≤ Q ^ 52 := by
  unfold ordF4
  calc Q ^ 24 * (Q ^ 12 - 1) * (Q ^ 8 - 1) * (Q ^ 6 - 1) * (Q ^ 2 - 1)
      ≤ Q ^ 24 * Q ^ 12 * Q ^ 8 * Q ^ 6 * Q ^ 2 := by gcongr <;> exact Nat.sub_le _ _
    _ = Q ^ 52 := by ring

theorem ordE6_le (Q : ℕ) : ordE6 Q ≤ Q ^ 78 := by
  unfold ordE6
  refine (Nat.div_le_self _ _).trans ?_
  calc Q ^ 36 * (Q ^ 12 - 1) * (Q ^ 9 - 1) * (Q ^ 8 - 1) * (Q ^ 6 - 1) * (Q ^ 5 - 1) * (Q ^ 2 - 1)
      ≤ Q ^ 36 * Q ^ 12 * Q ^ 9 * Q ^ 8 * Q ^ 6 * Q ^ 5 * Q ^ 2 := by
        gcongr <;> exact Nat.sub_le _ _
    _ = Q ^ 78 := by ring

theorem ordTwistedE6_le (Q : ℕ) (hQ : 2 ≤ Q) : ordTwistedE6 Q ≤ Q ^ 80 := by
  unfold ordTwistedE6
  refine (Nat.div_le_self _ _).trans ?_
  have h9 : Q ^ 9 + 1 ≤ Q ^ 10 := by
    have : 1 ≤ Q ^ 9 := Nat.one_le_pow _ _ (by omega)
    calc Q ^ 9 + 1 ≤ Q ^ 9 * Q := by nlinarith
      _ = Q ^ 10 := (pow_succ _ _).symm
  have h5 : Q ^ 5 + 1 ≤ Q ^ 6 := by
    have : 1 ≤ Q ^ 5 := Nat.one_le_pow _ _ (by omega)
    calc Q ^ 5 + 1 ≤ Q ^ 5 * Q := by nlinarith
      _ = Q ^ 6 := (pow_succ _ _).symm
  calc Q ^ 36 * (Q ^ 12 - 1) * (Q ^ 9 + 1) * (Q ^ 8 - 1) * (Q ^ 6 - 1) * (Q ^ 5 + 1) * (Q ^ 2 - 1)
      ≤ Q ^ 36 * Q ^ 12 * Q ^ 10 * Q ^ 8 * Q ^ 6 * Q ^ 6 * Q ^ 2 := by
        gcongr <;> exact Nat.sub_le _ _
    _ = Q ^ 80 := by ring

theorem ordE7_le (Q : ℕ) : ordE7 Q ≤ Q ^ 133 := by
  unfold ordE7
  refine (Nat.div_le_self _ _).trans ?_
  calc Q ^ 63 * (Q ^ 18 - 1) * (Q ^ 14 - 1) * (Q ^ 12 - 1) * (Q ^ 10 - 1) * (Q ^ 8 - 1) *
        (Q ^ 6 - 1) * (Q ^ 2 - 1)
      ≤ Q ^ 63 * Q ^ 18 * Q ^ 14 * Q ^ 12 * Q ^ 10 * Q ^ 8 * Q ^ 6 * Q ^ 2 := by
        gcongr <;> exact Nat.sub_le _ _
    _ = Q ^ 133 := by ring

theorem ordE8_le (Q : ℕ) : ordE8 Q ≤ Q ^ 248 := by
  unfold ordE8
  calc Q ^ 120 * (Q ^ 30 - 1) * (Q ^ 24 - 1) * (Q ^ 20 - 1) * (Q ^ 18 - 1) * (Q ^ 14 - 1) *
        (Q ^ 12 - 1) * (Q ^ 8 - 1) * (Q ^ 2 - 1)
      ≤ Q ^ 120 * Q ^ 30 * Q ^ 24 * Q ^ 20 * Q ^ 18 * Q ^ 14 * Q ^ 12 * Q ^ 8 * Q ^ 2 := by
        gcongr <;> exact Nat.sub_le _ _
    _ = Q ^ 248 := by ring

theorem pow_four_le_of {o f E c : ℕ} (h : o ≤ (2 ^ f) ^ E) (hE : 4 * E ≤ 11 * c) :
    o ^ 4 ≤ (2 ^ (f * c)) ^ 11 := by
  calc o ^ 4 ≤ ((2 ^ f) ^ E) ^ 4 := Nat.pow_le_pow_left h 4
    _ = 2 ^ (f * (4 * E)) := by rw [← pow_mul, ← pow_mul]; ring_nf
    _ ≤ 2 ^ (f * (11 * c)) := Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left f hE)
    _ = (2 ^ (f * c)) ^ 11 := by rw [← pow_mul]; ring_nf

end CFSG.RankThree.PartOne.F106
