module

public import CFSG.Open.Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open

theorem w183art_gcd_mul_ordA_one {x : ℕ} (hx : 1 ≤ x) :
    Nat.gcd 2 (x - 1) * ordA 1 x = x * (x ^ 2 - 1) := by
  have hp : (∏ i ∈ Finset.Icc 2 (1 + 1), (x ^ i - 1)) = x ^ 2 - 1 := by
    have e : Finset.Icc 2 (1 + 1) = {2} := by decide
    rw [e]; simp
  have hdvd : Nat.gcd (1 + 1) (x - 1) ∣
      x ^ (1 * (1 + 1) / 2) * (x ^ 2 - 1) := by
    have h1 : Nat.gcd (1 + 1) (x - 1) ∣ x - 1 := Nat.gcd_dvd_right _ _
    have h2 : x - 1 ∣ x ^ 2 - 1 := by
      simpa using Nat.sub_dvd_pow_sub_pow x 1 2
    exact Dvd.dvd.mul_left (h1.trans h2) _
  unfold ordA
  rw [hp]
  have h := Nat.mul_div_cancel' hdvd
  norm_num at h ⊢
  exact h

theorem w183art_gcd_mul_ordA_two {p : ℕ} (hp : 1 ≤ p) :
    Nat.gcd 3 (p - 1) * ordA 2 p = p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 - 1)) := by
  have hprod : (∏ i ∈ Finset.Icc 2 (2 + 1), (p ^ i - 1)) =
      (p ^ 2 - 1) * (p ^ 3 - 1) := by
    have e : Finset.Icc 2 (2 + 1) = {2, 3} := by decide
    rw [e]; simp
  have hdvd : Nat.gcd (2 + 1) (p - 1) ∣
      p ^ (2 * (2 + 1) / 2) * ((p ^ 2 - 1) * (p ^ 3 - 1)) := by
    have h1 : Nat.gcd (2 + 1) (p - 1) ∣ p - 1 := Nat.gcd_dvd_right _ _
    have h2 : p - 1 ∣ p ^ 2 - 1 := by
      simpa using Nat.sub_dvd_pow_sub_pow p 1 2
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (h1.trans h2) _) _
  unfold ordA
  rw [hprod]
  have h := Nat.mul_div_cancel' hdvd
  norm_num at h ⊢
  exact h

theorem w183art_gcd_mul_ordTwistedA_two {p : ℕ} :
    Nat.gcd 3 (p + 1) * ordTwistedA 2 p = p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 + 1)) := by
  have hprod : (∏ i ∈ Finset.Icc 2 (2 + 1), ((p : ℤ) ^ i - (-1 : ℤ) ^ i).toNat) =
      (p ^ 2 - 1) * (p ^ 3 + 1) := by
    have e : Finset.Icc 2 (2 + 1) = {2, 3} := by decide
    rw [e]
    simp only [Finset.mem_insert, Finset.mem_singleton, or_self, not_false_eq_true,
      Finset.prod_insert, Finset.prod_singleton, show (3 : ℕ) ≠ 4 by decide,
      show (2 : ℕ) ≠ 3 by decide, show (2 : ℕ) ≠ 4 by decide]
    have h2 : ((p : ℤ) ^ 2 - (-1 : ℤ) ^ 2).toNat = p ^ 2 - 1 := by
      have hh : ((p : ℤ) ^ 2 - (-1 : ℤ) ^ 2) = ((p ^ 2 : ℕ) : ℤ) - 1 := by
        push_cast; ring
      rw [hh]; omega
    have h3 : ((p : ℤ) ^ 3 - (-1 : ℤ) ^ 3).toNat = p ^ 3 + 1 := by
      have hh : ((p : ℤ) ^ 3 - (-1 : ℤ) ^ 3) = ((p ^ 3 + 1 : ℕ) : ℤ) := by
        push_cast; ring
      rw [hh]; exact Int.toNat_natCast _
    rw [h2, h3]
  have hdvd : Nat.gcd (2 + 1) (p + 1) ∣
      p ^ (2 * (2 + 1) / 2) * ((p ^ 2 - 1) * (p ^ 3 + 1)) := by
    have h1 : Nat.gcd (2 + 1) (p + 1) ∣ p + 1 := Nat.gcd_dvd_right _ _
    have h2 : p + 1 ∣ p ^ 3 + 1 := by
      simpa using (Odd.nat_add_dvd_pow_add_pow p 1 (n := 3) (by decide : Odd 3))
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_left (h1.trans h2) _) _
  unfold ordTwistedA
  rw [hprod]
  have h := Nat.mul_div_cancel' hdvd
  norm_num at h ⊢
  exact h

theorem w183art_gcd_mul_ordBC {n q : ℕ} (hn : 1 ≤ n) :
    Nat.gcd 2 (q - 1) * ordBC n q = q ^ (n * n) * ∏ i ∈ Finset.Icc 1 n, (q ^ (2 * i) - 1) := by
  have hdvd : Nat.gcd 2 (q - 1) ∣
      q ^ (n * n) * ∏ i ∈ Finset.Icc 1 n, (q ^ (2 * i) - 1) := by
    have h1 : Nat.gcd 2 (q - 1) ∣ q - 1 := Nat.gcd_dvd_right _ _
    have h2 : q - 1 ∣ q ^ (2 * 1) - 1 := by
      simpa using Nat.sub_dvd_pow_sub_pow q 1 (2 * 1)
    have hmem : (1 : ℕ) ∈ Finset.Icc 1 n := Finset.mem_Icc.2 ⟨le_rfl, hn⟩
    have h3 : q - 1 ∣ ∏ i ∈ Finset.Icc 1 n, (q ^ (2 * i) - 1) :=
      h2.trans (Finset.dvd_prod_of_mem _ hmem)
    exact Dvd.dvd.mul_left (h1.trans h3) _
  unfold ordBC
  exact Nat.mul_div_cancel' hdvd

theorem w183art_gcd_mul_ordD {n q : ℕ} (hn : 1 ≤ n) :
    Nat.gcd 4 (q ^ n - 1) * ordD n q =
      q ^ (n * (n - 1)) * ((q ^ n - 1) * ∏ i ∈ Finset.Icc 1 (n - 1), (q ^ (2 * i) - 1)) := by
  have hdvd : Nat.gcd 4 (q ^ n - 1) ∣
      q ^ (n * (n - 1)) * ((q ^ n - 1) *
        ∏ i ∈ Finset.Icc 1 (n - 1), (q ^ (2 * i) - 1)) := by
    have h1 : Nat.gcd 4 (q ^ n - 1) ∣ q ^ n - 1 := Nat.gcd_dvd_right _ _
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_right h1 _) _
  unfold ordD
  rw [mul_assoc]
  exact Nat.mul_div_cancel' hdvd

theorem w183art_gcd_mul_ordTwistedD {n q : ℕ} (hn : 1 ≤ n) :
    Nat.gcd 4 (q ^ n + 1) * ordTwistedD n q =
      q ^ (n * (n - 1)) * ((q ^ n + 1) * ∏ i ∈ Finset.Icc 1 (n - 1), (q ^ (2 * i) - 1)) := by
  have hdvd : Nat.gcd 4 (q ^ n + 1) ∣
      q ^ (n * (n - 1)) * ((q ^ n + 1) *
        ∏ i ∈ Finset.Icc 1 (n - 1), (q ^ (2 * i) - 1)) := by
    have h1 : Nat.gcd 4 (q ^ n + 1) ∣ q ^ n + 1 := Nat.gcd_dvd_right _ _
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_right h1 _) _
  unfold ordTwistedD
  rw [mul_assoc]
  exact Nat.mul_div_cancel' hdvd

end CFSG.LocalAnalysis.WeakClosure81
