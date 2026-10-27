module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.AltSevenNotLie
public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupNum

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput lieOrderNumerator lieOrderDivisor
  lieSylowExponent)

private theorem w183_mono_sub_mul_add {x y : ℕ} (h : x ≤ y) :
    (x - 1) * (x + 1) ≤ (y - 1) * (y + 1) :=
  Nat.mul_le_mul (Nat.sub_le_sub_right h 1) (Nat.add_le_add_right h 1)

theorem w183_alt_factorial_ne_psl2 {p e n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : 9 < p ^ e)
    (hn : n = 5 ∨ n = 6 ∨ n = 8)
    (h : p ^ e * ((p ^ e - 1) * (p ^ e + 1)) = n.factorial) : False := by
  have hodd : Odd (p ^ e) := (hp.odd_of_ne_two hp2).pow
  have hge : 11 ≤ p ^ e := by
    obtain ⟨k, hk⟩ := hodd
    omega
  rcases hn with rfl | rfl | rfl
  · have hle : 11 * ((11 - 1) * (11 + 1)) ≤ p ^ e * ((p ^ e - 1) * (p ^ e + 1)) :=
      Nat.mul_le_mul hge (w183_mono_sub_mul_add hge)
    rw [h] at hle
    norm_num at hle
  · have hle : 11 * ((11 - 1) * (11 + 1)) ≤ p ^ e * ((p ^ e - 1) * (p ^ e + 1)) :=
      Nat.mul_le_mul hge (w183_mono_sub_mul_add hge)
    rw [h] at hle
    norm_num at hle
  · by_cases hx : p ^ e ≤ 34
    · have hle : p ^ e * ((p ^ e - 1) * (p ^ e + 1)) ≤ 34 * ((34 - 1) * (34 + 1)) :=
        Nat.mul_le_mul hx (w183_mono_sub_mul_add hx)
      rw [h] at hle
      norm_num at hle
    · have hx35 : 35 ≤ p ^ e := by omega
      have hle : 35 * ((35 - 1) * (35 + 1)) ≤ p ^ e * ((p ^ e - 1) * (p ^ e + 1)) :=
        Nat.mul_le_mul hx35 (w183_mono_sub_mul_add hx35)
      rw [h] at hle
      norm_num at hle

private theorem w183_prime_pow_dvd_small {p k m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hm : m = 60 ∨ m = 360 ∨ m = 20160) (hk : k = 3 ∨ k = 4) (hdvd : p ^ k ∣ m) : False := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  rcases hk with rfl | rfl
  · have hp27 : p ≤ 27 := by
      by_contra h
      push Not at h
      have h28 : 28 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left (by omega) 3
      have hle : p ^ 3 ≤ m :=
        Nat.le_of_dvd (by rcases hm with rfl | rfl | rfl <;> norm_num) hdvd
      rcases hm with rfl | rfl | rfl <;> (norm_num at h28 hle; omega)
    rcases hm with rfl | rfl | rfl <;>
      (interval_cases p <;> first | exact absurd hp (by decide) | exact absurd hdvd (by decide))
  · have hp11 : p ≤ 11 := by
      by_contra h
      push Not at h
      have h12 : 12 ^ 4 ≤ p ^ 4 := Nat.pow_le_pow_left (by omega) 4
      have hle : p ^ 4 ≤ m :=
        Nat.le_of_dvd (by rcases hm with rfl | rfl | rfl <;> norm_num) hdvd
      rcases hm with rfl | rfl | rfl <;> (norm_num at h12 hle; omega)
    rcases hm with rfl | rfl | rfl <;>
      (interval_cases p <;> first | exact absurd hp (by decide) | exact absurd hdvd (by decide))

theorem w183_factorial_factorization {p N n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hn : n = 5 ∨ n = 6 ∨ n = 8) (hN : N = 3 ∨ N = 4)
    (h : (n.factorial / 2).factorization p = N) : False := by
  rcases hn with rfl | rfl | rfl
  · norm_num at h
    have hdvd : p ^ N ∣ 60 :=
      (hp.pow_dvd_iff_le_factorization (by norm_num)).2 (by omega)
    exact w183_prime_pow_dvd_small hp hp2 (Or.inl rfl) hN hdvd
  · norm_num at h
    have hdvd : p ^ N ∣ 360 :=
      (hp.pow_dvd_iff_le_factorization (by norm_num)).2 (by omega)
    exact w183_prime_pow_dvd_small hp hp2 (Or.inr (Or.inl rfl)) hN hdvd
  · norm_num at h
    have hdvd : p ^ N ∣ 20160 :=
      (hp.pow_dvd_iff_le_factorization (by norm_num)).2 (by omega)
    exact w183_prime_pow_dvd_small hp hp2 (Or.inr (Or.inr rfl)) hN hdvd

private theorem w183_orders_ne {a d1 d2 n1 n2 : ℕ} (h1 : a * d1 = n1) (h2 : a * d2 = n2)
    (h : n1 * d2 ≠ n2 * d1) : False := by
  apply h
  calc n1 * d2 = (a * d1) * d2 := by rw [h1]
    _ = (a * d2) * d1 := by ring
    _ = n2 * d1 := by rw [h2]

private theorem w183_pow_add_one_lt_pow {p a b : ℕ} (hp : 3 ≤ p) (ha : 1 ≤ a) (h : a + 1 ≤ b) :
    p ^ a + 1 < p ^ b := by
  have h1 : p ^ a + 1 < p ^ a * p := by
    have h3 : p ^ a * 3 ≤ p ^ a * p := Nat.mul_le_mul_left _ hp
    have h4 : 3 ≤ p ^ a := by
      obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
      rw [pow_succ]
      have : 1 ≤ p ^ b := Nat.one_le_pow _ _ (by omega)
      nlinarith
    nlinarith
  calc p ^ a + 1 < p ^ a * p := h1
    _ = p ^ (a + 1) := (pow_succ _ _).symm
    _ ≤ p ^ b := Nat.pow_le_pow_right (by omega) h

theorem w183_psl2_psp2_ne {p e M : ℕ} (hp35 : p = 3 ∨ p = 5) (he : e = 4)
    (hM_leaf : M * lieOrderDivisor .PSL 2 (p ^ e) = lieOrderNumerator .PSL 2 (p ^ e))
    (hM_c : M * lieOrderDivisor .PSp 2 (p ^ 1) = lieOrderNumerator .PSp 2 (p ^ 1)) : False := by
  subst he
  refine w183_orders_ne hM_leaf hM_c ?_
  rcases hp35 with rfl | rfl <;> decide

theorem w183_psl2_psl4_ne {p e M : ℕ} (hp35 : p = 3 ∨ p = 5) (he : e = 6)
    (hM_leaf : M * lieOrderDivisor .PSL 2 (p ^ e) = lieOrderNumerator .PSL 2 (p ^ e))
    (hM_c : M * lieOrderDivisor .PSL 4 (p ^ 1) = lieOrderNumerator .PSL 4 (p ^ 1)) : False := by
  subst he
  refine w183_orders_ne hM_leaf hM_c ?_
  rcases hp35 with rfl | rfl <;> decide

theorem w183_psl2_psu4_ne {p e M : ℕ} (hp35 : p = 3 ∨ p = 5) (he : e = 6)
    (hM_leaf : M * lieOrderDivisor .PSL 2 (p ^ e) = lieOrderNumerator .PSL 2 (p ^ e))
    (hM_c : M * lieOrderDivisor .PSU 4 (p ^ 1) = lieOrderNumerator .PSU 4 (p ^ 1)) : False := by
  subst he
  refine w183_orders_ne hM_leaf hM_c ?_
  rcases hp35 with rfl | rfl <;> decide

private theorem w183_lieOrderDivisor_PSL_two_odd {q : ℕ} (hq : Odd q) :
    lieOrderDivisor .PSL 2 q = 2 := by
  show Nat.gcd 2 (q - 1) = 2
  refine Nat.gcd_eq_left ?_
  obtain ⟨k, rfl⟩ := hq
  exact ⟨k, by omega⟩

private theorem w183_two_le_gcd_four_sub_one {q : ℕ} (hq : Odd q) :
    2 ≤ Nat.gcd 4 (q - 1) := by
  have h2 : 2 ∣ q - 1 := by
    obtain ⟨k, rfl⟩ := hq
    exact ⟨k, by omega⟩
  exact Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ (by norm_num))
    (Nat.dvd_gcd (by norm_num) h2)

private theorem w183_two_le_gcd_four_add_one {q : ℕ} (hq : Odd q) :
    2 ≤ Nat.gcd 4 (q + 1) := by
  have h2 : 2 ∣ q + 1 := by
    obtain ⟨k, rfl⟩ := hq
    exact ⟨k + 1, by ring⟩
  exact Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ (by norm_num))
    (Nat.dvd_gcd (by norm_num) h2)

theorem w183_psl2_pomegaOdd_ne {p e n M : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 3 ≤ n)
    (he : e = n ^ 2)
    (hM_leaf : M * lieOrderDivisor .PSL 2 (p ^ e) = lieOrderNumerator .PSL 2 (p ^ e))
    (hM_c : M * lieOrderDivisor .POmegaOdd n (p ^ 1) = lieOrderNumerator .POmegaOdd n (p ^ 1)) :
    False := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hodd : Odd (p ^ e) := (hp.odd_of_ne_two hp2).pow
  have hleaf : M * 2 = p ^ e * ((p ^ e) ^ 2 - 1) := by
    have hD : lieOrderDivisor .PSL 2 (p ^ e) = 2 := w183_lieOrderDivisor_PSL_two_odd hodd
    have hN : lieOrderNumerator .PSL 2 (p ^ e) = p ^ e * ((p ^ e) ^ 2 - 1) := by
      simp [lieOrderNumerator, Finset.prod_pair]
    rw [hD, hN] at hM_leaf
    exact hM_leaf
  have hc : M * 2 = p ^ (n ^ 2) * ∏ i ∈ Finset.Icc 1 n, (p ^ (2 * i) - 1) := by
    have hNc : lieOrderNumerator .POmegaOdd n (p ^ 1) =
        p ^ (n ^ 2) * ∏ i ∈ Finset.Icc 1 n, (p ^ (2 * i) - 1) := by
      simp [lieOrderNumerator]
    rw [hNc] at hM_c
    simpa [lieOrderDivisor] using hM_c
  have heq : p ^ e * ((p ^ e) ^ 2 - 1) = p ^ (n ^ 2) * ∏ i ∈ Finset.Icc 1 n, (p ^ (2 * i) - 1) := by
    rw [← hleaf, ← hc]
  subst he
  have hcof_eq : (p ^ (n ^ 2)) ^ 2 - 1 = ∏ i ∈ Finset.Icc 1 n, (p ^ (2 * i) - 1) :=
    Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos _) heq
  have hcof_le : (∏ i ∈ Finset.Icc 1 n, (p ^ (2 * i) - 1)) ≤ p ^ (n * (n + 1)) :=
    CFSG.OddStandard.AltStdSec.cof_prod_two_mul_le p n
  have hlt : p ^ (n * (n + 1)) < (p ^ (n ^ 2)) ^ 2 - 1 := by
    rw [show (p ^ (n ^ 2)) ^ 2 = p ^ (2 * n ^ 2) by rw [← pow_mul]; ring]
    have h := w183_pow_add_one_lt_pow hp3 (a := n * (n + 1)) (b := 2 * n ^ 2)
      (by nlinarith) (by nlinarith)
    omega
  omega

theorem w183_psl2_pomegaPlus_ne {p e n M : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 4 ≤ n)
    (he : e = n * (n - 1))
    (hM_leaf : M * lieOrderDivisor .PSL 2 (p ^ e) = lieOrderNumerator .PSL 2 (p ^ e))
    (hM_c : M * lieOrderDivisor .POmegaPlus n (p ^ 1) = lieOrderNumerator .POmegaPlus n (p ^ 1)) :
    False := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hodd : Odd (p ^ e) := (hp.odd_of_ne_two hp2).pow
  have hoddp : Odd (p ^ 1) := by simpa using hp.odd_of_ne_two hp2
  have hleaf : M * 2 = p ^ e * ((p ^ e) ^ 2 - 1) := by
    have hD : lieOrderDivisor .PSL 2 (p ^ e) = 2 := w183_lieOrderDivisor_PSL_two_odd hodd
    have hN : lieOrderNumerator .PSL 2 (p ^ e) = p ^ e * ((p ^ e) ^ 2 - 1) := by
      simp [lieOrderNumerator, Finset.prod_pair]
    rw [hD, hN] at hM_leaf
    exact hM_leaf
  set A := n * (n - 1) with hA
  set cof := (p ^ n - 1) * ∏ i ∈ Finset.Icc 1 (n - 1), (p ^ (2 * i) - 1) with hcof
  have hDc : lieOrderDivisor .POmegaPlus n (p ^ 1) = Nat.gcd 4 ((p ^ 1) ^ n - 1) := rfl
  have hDc2 : 2 ≤ lieOrderDivisor .POmegaPlus n (p ^ 1) := by
    rw [hDc]
    exact w183_two_le_gcd_four_sub_one (by simpa using hoddp.pow)
  have hNc : lieOrderNumerator .POmegaPlus n (p ^ 1) = p ^ A * cof := by
    simp only [lieOrderNumerator]
    rw [hA, hcof]
    ring
  have hc : M * lieOrderDivisor .POmegaPlus n (p ^ 1) = p ^ A * cof := by
    rw [hNc] at hM_c; exact hM_c
  have hkey : (p ^ A * ((p ^ A) ^ 2 - 1)) * lieOrderDivisor .POmegaPlus n (p ^ 1) =
      (p ^ A * cof) * 2 := by
    rw [he] at hleaf
    rw [← hleaf, ← hc]
    ring
  have hkey2 : ((p ^ A) ^ 2 - 1) * lieOrderDivisor .POmegaPlus n (p ^ 1) = cof * 2 := by
    have h' : p ^ A * (((p ^ A) ^ 2 - 1) * lieOrderDivisor .POmegaPlus n (p ^ 1)) =
        p ^ A * (cof * 2) := by
      simpa only [mul_assoc] using hkey
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos A) h'
  have hcof_le : cof ≤ p ^ (n ^ 2) := by
    rw [hcof]
    calc (p ^ n - 1) * ∏ i ∈ Finset.Icc 1 (n - 1), (p ^ (2 * i) - 1)
        ≤ p ^ n * p ^ ((n - 1) * ((n - 1) + 1)) :=
          Nat.mul_le_mul (Nat.sub_le _ _) (CFSG.OddStandard.AltStdSec.cof_prod_two_mul_le p (n - 1))
      _ = p ^ (n + (n - 1) * ((n - 1) + 1)) := (pow_add _ _ _).symm
      _ ≤ p ^ (n ^ 2) := by
        refine Nat.pow_le_pow_right (by omega) ?_
        have h1 : 1 ≤ n := by omega
        zify [h1]
        nlinarith
  have hlt : p ^ (n ^ 2) < (p ^ A) ^ 2 - 1 := by
    rw [hA, show (p ^ (n * (n - 1))) ^ 2 = p ^ (2 * (n * (n - 1))) by rw [← pow_mul]; ring]
    have hle : n ^ 2 + 1 ≤ 2 * (n * (n - 1)) := by
      have h1 : 1 ≤ n := by omega
      zify [h1]
      nlinarith
    have h := w183_pow_add_one_lt_pow hp3 (a := n ^ 2) (b := 2 * (n * (n - 1)))
      (by nlinarith) hle
    omega
  have hLHS : 2 * ((p ^ A) ^ 2 - 1) ≤
      ((p ^ A) ^ 2 - 1) * lieOrderDivisor .POmegaPlus n (p ^ 1) := by
    nlinarith [hDc2, Nat.zero_le ((p ^ A) ^ 2 - 1)]
  omega

theorem w183_psl2_pomegaMinus_ne {p e n M : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 4 ≤ n)
    (he : e = n * (n - 1))
    (hM_leaf : M * lieOrderDivisor .PSL 2 (p ^ e) = lieOrderNumerator .PSL 2 (p ^ e))
    (hM_c : M * lieOrderDivisor .POmegaMinus n (p ^ 1) = lieOrderNumerator .POmegaMinus n (p ^ 1)) :
    False := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hodd : Odd (p ^ e) := (hp.odd_of_ne_two hp2).pow
  have hoddp : Odd (p ^ 1) := by simpa using hp.odd_of_ne_two hp2
  have hleaf : M * 2 = p ^ e * ((p ^ e) ^ 2 - 1) := by
    have hD : lieOrderDivisor .PSL 2 (p ^ e) = 2 := w183_lieOrderDivisor_PSL_two_odd hodd
    have hN : lieOrderNumerator .PSL 2 (p ^ e) = p ^ e * ((p ^ e) ^ 2 - 1) := by
      simp [lieOrderNumerator, Finset.prod_pair]
    rw [hD, hN] at hM_leaf
    exact hM_leaf
  set A := n * (n - 1) with hA
  set cof := (p ^ n + 1) * ∏ i ∈ Finset.Icc 1 (n - 1), (p ^ (2 * i) - 1) with hcof
  have hDc : lieOrderDivisor .POmegaMinus n (p ^ 1) = Nat.gcd 4 ((p ^ 1) ^ n + 1) := rfl
  have hDc2 : 2 ≤ lieOrderDivisor .POmegaMinus n (p ^ 1) := by
    rw [hDc]
    exact w183_two_le_gcd_four_add_one (by simpa using hoddp.pow)
  have hNc : lieOrderNumerator .POmegaMinus n (p ^ 1) = p ^ A * cof := by
    simp only [lieOrderNumerator]
    rw [hA, hcof]
    ring
  have hc : M * lieOrderDivisor .POmegaMinus n (p ^ 1) = p ^ A * cof := by
    rw [hNc] at hM_c; exact hM_c
  have hkey : (p ^ A * ((p ^ A) ^ 2 - 1)) * lieOrderDivisor .POmegaMinus n (p ^ 1) =
      (p ^ A * cof) * 2 := by
    rw [he] at hleaf
    rw [← hleaf, ← hc]
    ring
  have hkey2 : ((p ^ A) ^ 2 - 1) * lieOrderDivisor .POmegaMinus n (p ^ 1) = cof * 2 := by
    have h' : p ^ A * (((p ^ A) ^ 2 - 1) * lieOrderDivisor .POmegaMinus n (p ^ 1)) =
        p ^ A * (cof * 2) := by
      simpa only [mul_assoc] using hkey
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos A) h'
  have hcof_le : cof ≤ p ^ (n ^ 2 + 1) := by
    rw [hcof]
    calc (p ^ n + 1) * ∏ i ∈ Finset.Icc 1 (n - 1), (p ^ (2 * i) - 1)
        ≤ p ^ (n + 1) * p ^ ((n - 1) * ((n - 1) + 1)) :=
          Nat.mul_le_mul (CFSG.OddStandard.AltStdSec.cof_pow_add_one_le (by omega) n)
            (CFSG.OddStandard.AltStdSec.cof_prod_two_mul_le p (n - 1))
      _ = p ^ (n + 1 + (n - 1) * ((n - 1) + 1)) := (pow_add _ _ _).symm
      _ ≤ p ^ (n ^ 2 + 1) := by
        refine Nat.pow_le_pow_right (by omega) ?_
        have h1 : 1 ≤ n := by omega
        zify [h1]
        nlinarith
  have hlt : p ^ (n ^ 2 + 1) < (p ^ A) ^ 2 - 1 := by
    rw [hA, show (p ^ (n * (n - 1))) ^ 2 = p ^ (2 * (n * (n - 1))) by rw [← pow_mul]; ring]
    have hle : n ^ 2 + 1 + 1 ≤ 2 * (n * (n - 1)) := by
      have h1 : 1 ≤ n := by omega
      zify [h1]
      nlinarith
    have h := w183_pow_add_one_lt_pow hp3 (a := n ^ 2 + 1) (b := 2 * (n * (n - 1)))
      (by exact Nat.le_add_left 1 (n ^ 2)) hle
    omega
  have hLHS : 2 * ((p ^ A) ^ 2 - 1) ≤
      ((p ^ A) ^ 2 - 1) * lieOrderDivisor .POmegaMinus n (p ^ 1) := by
    nlinarith [hDc2, Nat.zero_le ((p ^ A) ^ 2 - 1)]
  omega

theorem w183_alt_seven_nine_false (hO : LieOrderFormulasInput) {T : Type} [Group T]
    {t : CFSG.Open.StatedLieTag} {m p g : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hmodel : LieModel T t m p g)
    {n : ℕ} (hn7 : n = 7 ∨ 9 ≤ n) (e : T ≃* alternatingGroup (Fin n)) : False := by
  have hoddT : CFSG.Blueprint.OddLieType T := ⟨t, m, p, g, hp, hp2, hmodel.admissible, hmodel⟩
  have hoddA : CFSG.Blueprint.OddLieType (alternatingGroup (Fin n)) :=
    ⟨t, m, p, g, hp, hp2, hmodel.admissible, LieModel.of_mulEquiv e hmodel⟩
  rcases hn7 with rfl | h9
  · exact CFSG.ComponentClassification.CatFC.not_oddLieType_alt7 hO hoddA
  · exact CFSG.OddStandard.AltStdSec.not_oddLieType_alt hO h9 hoddA

theorem w183_three_ne_sq {n : ℕ} (h : n ^ 2 = 3) : False := by
  have hn : n ≤ 1 := by
    by_contra hlt
    push Not at hlt
    have h4 : 2 ≤ n := by omega
    have h4' : 4 ≤ n ^ 2 := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ n ^ 2 := Nat.pow_le_pow_left h4 2
    omega
  interval_cases n <;> omega

theorem w183_three_ne_rect {n : ℕ} (h : n * (n - 1) = 3) : False := by
  have hn : n ≤ 3 := by
    by_contra hlt
    push Not at hlt
    have h4 : 4 ≤ n := by omega
    have h12 : 12 ≤ n * (n - 1) := by
      have : 3 ≤ n - 1 := by omega
      calc 12 = 4 * 3 := by norm_num
        _ ≤ n * (n - 1) := Nat.mul_le_mul h4 this
    omega
  interval_cases n <;> omega

end CFSG.LocalAnalysis.WeakClosure81

end
