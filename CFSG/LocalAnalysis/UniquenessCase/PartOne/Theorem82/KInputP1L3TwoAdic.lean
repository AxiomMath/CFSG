module

public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

theorem two_pow_three_le_of_dvd {v k x : ℕ} (hx : 0 < x) (h : 2 ^ v ∣ 2 ^ k * x) :
    2 ^ (3 * v) ≤ 2 ^ (3 * k) * x ^ 3 := by
  rcases Nat.lt_or_ge v k with hkv | hvk
  · have h1 : 2 ^ (3 * v) ≤ 2 ^ (3 * k) := pow_le_pow_right' (by norm_num) (by omega)
    have h2 : 1 ≤ x ^ 3 := Nat.one_le_pow _ _ (by omega)
    exact h1.trans (Nat.le_mul_of_pos_right _ (by omega))
  · have hvk' : v = k + (v - k) := by omega
    have h2 : 2 ^ (v - k) ∣ x := by
      have h3 : 2 ^ v = 2 ^ k * 2 ^ (v - k) := by
        nth_rewrite 1 [hvk']
        rw [pow_add]
      rw [h3] at h
      exact (Nat.mul_dvd_mul_iff_left (pow_pos (by norm_num : (0 : ℕ) < 2) k)).1 h
    have h4 : 2 ^ (v - k) ≤ x := Nat.le_of_dvd hx h2
    calc 2 ^ (3 * v) = 2 ^ (3 * k) * (2 ^ (v - k)) ^ 3 := by
          have e1 : 3 * v = 3 * k + 3 * (v - k) := by omega
          rw [e1, pow_add]
          have e2 : 3 * (v - k) = (v - k) * 3 := by ring
          rw [e2, ← pow_mul]
      _ ≤ 2 ^ (3 * k) * x ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h4 3)

theorem coprime_two_pow_of_odd {m v : ℕ} (hm : m % 2 = 1) : Nat.Coprime (2 ^ v) m :=
  Nat.Coprime.pow_left v (Nat.coprime_two_left.2 (Nat.odd_iff.2 hm))

theorem odd_psl_bracket {q : ℕ} (hq : q % 2 = 1) : Odd (q ^ 3 * (q ^ 2 + q + 1)) := by
  have hqo : Odd q := Nat.odd_iff.2 hq
  exact (hqo.pow (n := 3)).mul (((hqo.pow (n := 2)).add_odd hqo).add_one)

theorem odd_psu_bracket {q : ℕ} (hq : q % 2 = 1) : Odd (q ^ 3 * (q ^ 2 - q + 1)) := by
  have hqo : Odd q := Nat.odd_iff.2 hq
  exact (hqo.pow (n := 3)).mul (((hqo.pow (n := 2)).tsub_odd hqo).add_one)

theorem sq_sub_one (q : ℕ) : q ^ 2 - 1 = (q - 1) * (q + 1) := by
  simpa [mul_comm] using Nat.sq_sub_sq q 1

theorem cube_sub_one (q : ℕ) (hq : 1 ≤ q) : q ^ 3 - 1 = (q - 1) * (q ^ 2 + q + 1) := by
  have h := geom_sum_mul_of_one_le (x := q) hq 3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  rw [← h]; ring

theorem cube_add_one (q : ℕ) (hq : 1 ≤ q) : q ^ 3 + 1 = (q + 1) * (q ^ 2 - q + 1) := by
  obtain ⟨u, rfl⟩ : ∃ u, q = u + 1 := ⟨q - 1, by omega⟩
  have h : (u + 1) ^ 2 - (u + 1) + 1 = u ^ 2 + u + 1 := by
    have e : (u + 1) ^ 2 = u ^ 2 + 2 * u + 1 := by ring
    omega
  rw [h]; ring

theorem psl_factor (q : ℕ) (hq : 1 ≤ q) :
    q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))
      = (q ^ 3 * (q ^ 2 + q + 1)) * ((q - 1) ^ 2 * (q + 1)) := by
  rw [sq_sub_one q, cube_sub_one q hq]; ring

theorem psu_factor (q : ℕ) (hq : 1 ≤ q) :
    q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1))
      = (q ^ 3 * (q ^ 2 - q + 1)) * ((q - 1) * (q + 1) ^ 2) := by
  rw [sq_sub_one q, cube_add_one q hq]; ring

theorem psl_poly_one {q : ℕ} (h5 : 5 ≤ q) :
    8 * (q - 1) ^ 6 ≤ (q ^ 3 * (q ^ 2 + q + 1)) * ((q - 1) ^ 2 * (q + 1)) := by
  obtain ⟨t, rfl⟩ : ∃ t, q = t + 5 := ⟨q - 5, by omega⟩
  have h1 : t + 5 - 1 = t + 4 := by omega
  rw [h1]
  calc 8 * (t + 4) ^ 6
      ≤ 8 * (t + 4) ^ 6 + (339232 + 554048 * t + 396170 * t ^ 2 + 162011 * t ^ 3
          + 41430 * t ^ 4 + 6777 * t ^ 5 + 691 * t ^ 6 + 40 * t ^ 7 + t ^ 8) :=
        Nat.le_add_right _ _
    _ = ((t + 5) ^ 3 * ((t + 5) ^ 2 + (t + 5) + 1)) * ((t + 4) ^ 2 * (t + 5 + 1)) := by ring

theorem psl_poly_two {q : ℕ} (h5 : 5 ≤ q) :
    64 * (q + 1) ^ 3 ≤ (q ^ 3 * (q ^ 2 + q + 1)) * ((q - 1) ^ 2 * (q + 1)) := by
  obtain ⟨t, rfl⟩ : ∃ t, q = t + 5 := ⟨q - 5, by omega⟩
  have h1 : t + 5 - 1 = t + 4 := by omega
  rw [h1]
  calc 64 * (t + 5 + 1) ^ 3
      ≤ 64 * (t + 5 + 1) ^ 3 + (358176 + 596288 * t + 425738 * t ^ 2 + 172187 * t ^ 3
          + 43350 * t ^ 4 + 6969 * t ^ 5 + 699 * t ^ 6 + 40 * t ^ 7 + t ^ 8) :=
        Nat.le_add_right _ _
    _ = ((t + 5) ^ 3 * ((t + 5) ^ 2 + (t + 5) + 1)) * ((t + 4) ^ 2 * (t + 5 + 1)) := by ring

theorem psu_poly_one {q : ℕ} (h5 : 5 ≤ q) :
    64 * (q - 1) ^ 3 ≤ (q ^ 3 * (q ^ 2 - q + 1)) * ((q - 1) * (q + 1) ^ 2) := by
  obtain ⟨t, rfl⟩ : ∃ t, q = t + 5 := ⟨q - 5, by omega⟩
  have h1 : t + 5 - 1 = t + 4 := by omega
  have h2 : (t + 5) ^ 2 - (t + 5) + 1 = t ^ 2 + 9 * t + 21 := by
    have e : (t + 5) ^ 2 = t ^ 2 + 10 * t + 25 := by ring
    omega
  rw [h1, h2]
  calc 64 * (t + 4) ^ 3
      ≤ 64 * (t + 4) ^ 3 + (373904 + 606228 * t + 428592 * t ^ 2 + 172685 * t ^ 3
          + 43400 * t ^ 4 + 6971 * t ^ 5 + 699 * t ^ 6 + 40 * t ^ 7 + t ^ 8) :=
        Nat.le_add_right _ _
    _ = ((t + 5) ^ 3 * (t ^ 2 + 9 * t + 21)) * ((t + 4) * (t + 5 + 1) ^ 2) := by ring

theorem psu_poly_two {q : ℕ} (h5 : 5 ≤ q) :
    8 * (q + 1) ^ 6 ≤ (q ^ 3 * (q ^ 2 - q + 1)) * ((q - 1) * (q + 1) ^ 2) := by
  obtain ⟨t, rfl⟩ : ∃ t, q = t + 5 := ⟨q - 5, by omega⟩
  have h1 : t + 5 - 1 = t + 4 := by omega
  have h2 : (t + 5) ^ 2 - (t + 5) + 1 = t ^ 2 + 9 * t + 21 := by
    have e : (t + 5) ^ 2 = t ^ 2 + 10 * t + 25 := by ring
    omega
  rw [h1, h2]
  calc 8 * (t + 5 + 1) ^ 6
      ≤ 8 * (t + 5 + 1) ^ 6 + (4752 + 236052 * t + 273840 * t ^ 2 + 138189 * t ^ 3
          + 39080 * t ^ 4 + 6683 * t ^ 5 + 691 * t ^ 6 + 40 * t ^ 7 + t ^ 8) :=
        Nat.le_add_right _ _
    _ = ((t + 5) ^ 3 * (t ^ 2 + 9 * t + 21)) * ((t + 4) * (t + 5 + 1) ^ 2) := by ring

theorem psl_case_one {q v : ℕ} (hq4 : q % 4 = 1) (h5 : 5 ≤ q)
    (hv : 2 ^ v ∣ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))) :
    2 ^ (3 * v) ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
  have hq1 : 1 ≤ q := by omega
  have hq2 : q % 2 = 1 := by omega
  rw [psl_factor q hq1] at hv ⊢
  have hdiv : 2 ^ v ∣ (q - 1) ^ 2 * (q + 1) :=
    (coprime_two_pow_of_odd (Nat.odd_iff.1 (odd_psl_bracket hq2))).dvd_of_dvd_mul_left hv
  obtain ⟨B', hB'⟩ : ∃ B', q + 1 = 2 * B' := ⟨(q + 1) / 2, by omega⟩
  have hB'odd : B' % 2 = 1 := by omega
  have h2 : 2 ^ v ∣ 2 * (q - 1) ^ 2 := by
    have hcop : Nat.Coprime (2 ^ v) B' := coprime_two_pow_of_odd hB'odd
    have h3 : 2 ^ v ∣ (2 * (q - 1) ^ 2) * B' := by
      have e : (q - 1) ^ 2 * (q + 1) = (2 * (q - 1) ^ 2) * B' := by rw [hB']; ring
      rwa [e] at hdiv
    exact hcop.dvd_of_dvd_mul_right h3
  have hb := two_pow_three_le_of_dvd (k := 1) (x := (q - 1) ^ 2)
    (pow_pos (by omega : 0 < q - 1) 2) h2
  have hb' : 2 ^ (3 * v) ≤ 8 * (q - 1) ^ 6 := by
    have e : 2 ^ (3 * 1) * ((q - 1) ^ 2) ^ 3 = 8 * (q - 1) ^ 6 := by ring
    rwa [e] at hb
  exact hb'.trans (psl_poly_one h5)

theorem psl_case_three {q v : ℕ} (hq4 : q % 4 = 3) (h5 : 5 ≤ q)
    (hv : 2 ^ v ∣ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))) :
    2 ^ (3 * v) ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
  have hq1 : 1 ≤ q := by omega
  have hq2 : q % 2 = 1 := by omega
  rw [psl_factor q hq1] at hv ⊢
  have hdiv : 2 ^ v ∣ (q - 1) ^ 2 * (q + 1) :=
    (coprime_two_pow_of_odd (Nat.odd_iff.1 (odd_psl_bracket hq2))).dvd_of_dvd_mul_left hv
  obtain ⟨A', hA'⟩ : ∃ A', q - 1 = 2 * A' := ⟨(q - 1) / 2, by omega⟩
  have hA'odd : A' % 2 = 1 := by omega
  have h2 : 2 ^ v ∣ 4 * (q + 1) := by
    have hcop : Nat.Coprime (2 ^ v) (A' * A') :=
      Nat.Coprime.mul_right (coprime_two_pow_of_odd hA'odd) (coprime_two_pow_of_odd hA'odd)
    have h3 : 2 ^ v ∣ (4 * (q + 1)) * (A' * A') := by
      have e : (q - 1) ^ 2 * (q + 1) = (4 * (q + 1)) * (A' * A') := by rw [hA']; ring
      rwa [e] at hdiv
    exact hcop.dvd_of_dvd_mul_right h3
  have hb := two_pow_three_le_of_dvd (k := 2) (x := q + 1) (by omega) h2
  have hb' : 2 ^ (3 * v) ≤ 64 * (q + 1) ^ 3 := by
    have e : 2 ^ (3 * 2) * (q + 1) ^ 3 = 64 * (q + 1) ^ 3 := by norm_num
    rwa [e] at hb
  exact hb'.trans (psl_poly_two h5)

theorem psu_case_one {q v : ℕ} (hq4 : q % 4 = 1) (h5 : 5 ≤ q)
    (hv : 2 ^ v ∣ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1))) :
    2 ^ (3 * v) ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
  have hq1 : 1 ≤ q := by omega
  have hq2 : q % 2 = 1 := by omega
  rw [psu_factor q hq1] at hv ⊢
  have hdiv : 2 ^ v ∣ (q - 1) * (q + 1) ^ 2 :=
    (coprime_two_pow_of_odd (Nat.odd_iff.1 (odd_psu_bracket hq2))).dvd_of_dvd_mul_left hv
  obtain ⟨B', hB'⟩ : ∃ B', q + 1 = 2 * B' := ⟨(q + 1) / 2, by omega⟩
  have hB'odd : B' % 2 = 1 := by omega
  have h2 : 2 ^ v ∣ 4 * (q - 1) := by
    have hcop : Nat.Coprime (2 ^ v) (B' * B') :=
      Nat.Coprime.mul_right (coprime_two_pow_of_odd hB'odd) (coprime_two_pow_of_odd hB'odd)
    have h3 : 2 ^ v ∣ (4 * (q - 1)) * (B' * B') := by
      have e : (q - 1) * (q + 1) ^ 2 = (4 * (q - 1)) * (B' * B') := by rw [hB']; ring
      rwa [e] at hdiv
    exact hcop.dvd_of_dvd_mul_right h3
  have hb := two_pow_three_le_of_dvd (k := 2) (x := q - 1) (by omega) h2
  have hb' : 2 ^ (3 * v) ≤ 64 * (q - 1) ^ 3 := by
    have e : 2 ^ (3 * 2) * (q - 1) ^ 3 = 64 * (q - 1) ^ 3 := by norm_num
    rwa [e] at hb
  exact hb'.trans (psu_poly_one h5)

theorem psu_case_three {q v : ℕ} (hq4 : q % 4 = 3) (h5 : 5 ≤ q)
    (hv : 2 ^ v ∣ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1))) :
    2 ^ (3 * v) ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
  have hq1 : 1 ≤ q := by omega
  have hq2 : q % 2 = 1 := by omega
  rw [psu_factor q hq1] at hv ⊢
  have hdiv : 2 ^ v ∣ (q - 1) * (q + 1) ^ 2 :=
    (coprime_two_pow_of_odd (Nat.odd_iff.1 (odd_psu_bracket hq2))).dvd_of_dvd_mul_left hv
  obtain ⟨A', hA'⟩ : ∃ A', q - 1 = 2 * A' := ⟨(q - 1) / 2, by omega⟩
  have hA'odd : A' % 2 = 1 := by omega
  have h2 : 2 ^ v ∣ 2 * (q + 1) ^ 2 := by
    have hcop : Nat.Coprime (2 ^ v) A' := coprime_two_pow_of_odd hA'odd
    have h3 : 2 ^ v ∣ (2 * (q + 1) ^ 2) * A' := by
      have e : (q - 1) * (q + 1) ^ 2 = (2 * (q + 1) ^ 2) * A' := by rw [hA']; ring
      rwa [e] at hdiv
    exact hcop.dvd_of_dvd_mul_right h3
  have hb := two_pow_three_le_of_dvd (k := 1) (x := (q + 1) ^ 2)
    (pow_pos (by omega : 0 < q + 1) 2) h2
  have hb' : 2 ^ (3 * v) ≤ 8 * (q + 1) ^ 6 := by
    have e : 2 ^ (3 * 1) * ((q + 1) ^ 2) ^ 3 = 8 * (q + 1) ^ 6 := by ring
    rwa [e] at hb
  exact hb'.trans (psu_poly_two h5)

theorem two_pow_three_mul_le_psl {q v : ℕ} (hq : q % 2 = 1) (h5 : 5 ≤ q)
    (hv : 2 ^ v ∣ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))) :
    2 ^ (3 * v) ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
  by_cases h4 : q % 4 = 1
  · exact psl_case_one h4 h5 hv
  · exact psl_case_three (by omega) h5 hv

theorem two_pow_three_mul_le_psu {q v : ℕ} (hq : q % 2 = 1) (h5 : 5 ≤ q)
    (hv : 2 ^ v ∣ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1))) :
    2 ^ (3 * v) ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
  by_cases h4 : q % 4 = 1
  · exact psu_case_one h4 h5 hv
  · exact psu_case_three (by omega) h5 hv

theorem two_pow_three_mul_le {q c v : ℕ} (hq : q % 2 = 1) (h5 : 5 ≤ q)
    (hc : c = q ^ 3 - 1 ∨ c = q ^ 3 + 1) (hv : 2 ^ v ∣ q ^ 3 * ((q ^ 2 - 1) * c)) :
    2 ^ (3 * v) ≤ q ^ 3 * ((q ^ 2 - 1) * c) := by
  rcases hc with rfl | rfl
  · exact two_pow_three_mul_le_psl hq h5 hv
  · exact two_pow_three_mul_le_psu hq h5 hv

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
