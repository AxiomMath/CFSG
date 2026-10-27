module

public import CFSG.Open.StatedDefs
import CFSG.RankThree.SubgroupLists.UnitaryThreeFamily
import CFSG.ClassicalGroups.UnitaryFlag.GroupData
import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Matrix
open CFSG.Open (StatedSU)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.ClassicalGroups.UnitaryFlag

private theorem int_card_statedSU {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    {n : ℕ} (hn : 1 ≤ n) :
    (Nat.card (StatedSU n (p ^ f) K) : ℤ) =
      ((p ^ f : ℕ) : ℤ) ^ (n * (n - 1) / 2) *
        ∏ i ∈ Finset.Icc 2 n, (((p ^ f : ℕ) : ℤ) ^ i - (-1) ^ i) := by
  have hU := (CFSG.LinearGroups.unitary_full_group_order h
    (gramForm_isSymm h (G := (1 : Matrix (Fin n) (Fin n) K)) (by simp))
    (gramForm_separatingLeft h (by simp)) (Module.finrank_fin_fun K) hn).2.1
  rw [show StatedSU n (p ^ f) K = unitarySU p f K n from rfl, unitarySU_eq_gramSU h, card_gramSU,
    hU]

private theorem nat_card_statedSU_four {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) :
    Nat.card (StatedSU 4 (p ^ f) K) =
      (p ^ f) ^ 6 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) * ((p ^ f) ^ 4 - 1) := by
  have h1 := int_card_statedSU h (n := 4) (by norm_num)
  have hprod : ∏ i ∈ Finset.Icc 2 4, (((p ^ f : ℕ) : ℤ) ^ i - (-1) ^ i) =
      (((p ^ f : ℕ) : ℤ) ^ 2 - 1) * (((p ^ f : ℕ) : ℤ) ^ 3 + 1) *
        (((p ^ f : ℕ) : ℤ) ^ 4 - 1) := by
    rw [Finset.prod_Icc_succ_top (by norm_num : 2 ≤ 4),
      Finset.prod_Icc_succ_top (by norm_num : 2 ≤ 3)]
    simp
  rw [hprod] at h1
  have hq : 1 ≤ p ^ f := Nat.one_le_pow _ _ h.prime.pos
  have e2 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ hq
  have e4 : 1 ≤ (p ^ f) ^ 4 := Nat.one_le_pow _ _ hq
  zify [e2, e4]
  rw [h1]
  norm_num
  ring

private theorem nat_card_statedSU_five {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) :
    Nat.card (StatedSU 5 (p ^ f) K) =
      (p ^ f) ^ 10 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) * ((p ^ f) ^ 4 - 1) *
        ((p ^ f) ^ 5 + 1) := by
  have h1 := int_card_statedSU h (n := 5) (by norm_num)
  have hprod : ∏ i ∈ Finset.Icc 2 5, (((p ^ f : ℕ) : ℤ) ^ i - (-1) ^ i) =
      (((p ^ f : ℕ) : ℤ) ^ 2 - 1) * (((p ^ f : ℕ) : ℤ) ^ 3 + 1) *
        (((p ^ f : ℕ) : ℤ) ^ 4 - 1) * (((p ^ f : ℕ) : ℤ) ^ 5 + 1) := by
    rw [Finset.prod_Icc_succ_top (by norm_num : 2 ≤ 5),
      Finset.prod_Icc_succ_top (by norm_num : 2 ≤ 4),
      Finset.prod_Icc_succ_top (by norm_num : 2 ≤ 3)]
    simp
  rw [hprod] at h1
  have hq : 1 ≤ p ^ f := Nat.one_le_pow _ _ h.prime.pos
  have e2 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ hq
  have e4 : 1 ≤ (p ^ f) ^ 4 := Nat.one_le_pow _ _ hq
  zify [e2, e4]
  rw [h1]
  norm_num
  ring

private theorem factorization_three_prod_four {q : ℕ} (hq2 : 2 ≤ q) (hqmod : q % 3 = 1) :
    (q ^ 6 * (q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1)).factorization 3 =
      2 * (q - 1).factorization 3 := by
  have hq0 : q ≠ 0 := by omega
  have hA : q ^ 6 ≠ 0 := pow_ne_zero 6 hq0
  have hB : q ^ 2 - 1 ≠ 0 := by
    have : 4 ≤ q ^ 2 := by simpa using Nat.pow_le_pow_left hq2 2
    omega
  have hC : q ^ 3 + 1 ≠ 0 := by positivity
  have hD : q ^ 4 - 1 ≠ 0 := by
    have : 16 ≤ q ^ 4 := by simpa using Nat.pow_le_pow_left hq2 4
    omega
  have h3q : ¬ 3 ∣ q := by rw [Nat.dvd_iff_mod_eq_zero]; omega
  have h3qp1 : (q + 1).factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by
      intro hd
      rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, hqmod] at hd
      norm_num at hd)
  have h3q2p1 : (q ^ 2 + 1).factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by
      intro hd
      rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.pow_mod, hqmod] at hd
      norm_num at hd)
  have hfacC : (q ^ 3 + 1).factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by
      intro hd
      rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.pow_mod, hqmod] at hd
      norm_num at hd)
  have hfacA : (q ^ 6).factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (fun hd => h3q (Nat.prime_three.dvd_of_dvd_pow hd))
  have hfacB : (q ^ 2 - 1).factorization 3 = (q - 1).factorization 3 := by
    have hq2m1 : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      zify [(by omega : 1 ≤ q), (Nat.one_le_pow 2 q (by omega))]
      ring
    rw [hq2m1, Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply, h3qp1]
    simp
  have hfacD : (q ^ 4 - 1).factorization 3 = (q - 1).factorization 3 := by
    have hq4 : q ^ 4 - 1 = (q ^ 2 - 1) * (q ^ 2 + 1) := by
      zify [(by omega : 1 ≤ q), (Nat.one_le_pow 2 q (by omega)), (Nat.one_le_pow 4 q (by omega))]
      ring
    rw [hq4, Nat.factorization_mul hB (by positivity), Finsupp.add_apply, h3q2p1, hfacB]
    simp
  rw [Nat.factorization_mul (mul_ne_zero (mul_ne_zero hA hB) hC) hD,
    Nat.factorization_mul (mul_ne_zero hA hB) hC, Nat.factorization_mul hA hB]
  simp only [Finsupp.add_apply, hfacA, hfacB, hfacC, hfacD]
  ring

private theorem factorization_three_prod_five {q : ℕ} (hq2 : 2 ≤ q) (hqmod : q % 3 = 1) :
    (q ^ 10 * (q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1) * (q ^ 5 + 1)).factorization 3 =
      2 * (q - 1).factorization 3 := by
  have hq0 : q ≠ 0 := by omega
  have hA : q ^ 10 ≠ 0 := pow_ne_zero 10 hq0
  have hB : q ^ 2 - 1 ≠ 0 := by
    have : 4 ≤ q ^ 2 := by simpa using Nat.pow_le_pow_left hq2 2
    omega
  have hC : q ^ 3 + 1 ≠ 0 := by positivity
  have hD : q ^ 4 - 1 ≠ 0 := by
    have : 16 ≤ q ^ 4 := by simpa using Nat.pow_le_pow_left hq2 4
    omega
  have hE : q ^ 5 + 1 ≠ 0 := by positivity
  have h3q : ¬ 3 ∣ q := by rw [Nat.dvd_iff_mod_eq_zero]; omega
  have h3qp1 : (q + 1).factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by
      intro hd
      rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, hqmod] at hd
      norm_num at hd)
  have h3q2p1 : (q ^ 2 + 1).factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by
      intro hd
      rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.pow_mod, hqmod] at hd
      norm_num at hd)
  have h3q5p1 : (q ^ 5 + 1).factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by
      intro hd
      rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.pow_mod, hqmod] at hd
      norm_num at hd)
  have hfacC : (q ^ 3 + 1).factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by
      intro hd
      rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.pow_mod, hqmod] at hd
      norm_num at hd)
  have hfacA : (q ^ 10).factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (fun hd => h3q (Nat.prime_three.dvd_of_dvd_pow hd))
  have hfacB : (q ^ 2 - 1).factorization 3 = (q - 1).factorization 3 := by
    have hq2m1 : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      zify [(by omega : 1 ≤ q), (Nat.one_le_pow 2 q (by omega))]
      ring
    rw [hq2m1, Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply, h3qp1]
    simp
  have hfacD : (q ^ 4 - 1).factorization 3 = (q - 1).factorization 3 := by
    have hq4 : q ^ 4 - 1 = (q ^ 2 - 1) * (q ^ 2 + 1) := by
      zify [(by omega : 1 ≤ q), (Nat.one_le_pow 2 q (by omega)), (Nat.one_le_pow 4 q (by omega))]
      ring
    rw [hq4, Nat.factorization_mul hB (by positivity), Finsupp.add_apply, h3q2p1, hfacB]
    simp
  rw [Nat.factorization_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero hA hB) hC) hD) hE,
    Nat.factorization_mul (mul_ne_zero (mul_ne_zero hA hB) hC) hD,
    Nat.factorization_mul (mul_ne_zero hA hB) hC, Nat.factorization_mul hA hB]
  simp only [Finsupp.add_apply, hfacA, hfacB, hfacC, hfacD, h3q5p1]
  ring

theorem factorization_three_card_statedSU_two {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hq : p ^ f % 3 = 1) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 2) :
    (Nat.card (StatedSU 2 (p ^ f) K)).factorization 3 = (p ^ f - 1).factorization 3 := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have hK' : Nat.card K = p ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K p :=
    charP_of_card_eq_prime_pow (f := 2 * f) (by rwa [Nat.card_eq_fintype_card] at hK')
  set q := p ^ f with hqdef
  have hcard : Nat.card (StatedSU 2 (p ^ f) K) = q * (q ^ 2 - 1) := by
    rw [CFSG.RankThree.SubgroupLists.card_statedSU_two (K := K) (r := p) (f := f) hK, hqdef]
  have hqmod : q % 3 = 1 := by rw [hqdef]; exact hq
  have hq1 : 1 ≤ q := Nat.one_le_pow f p hp.pos
  have hq2 : 2 ≤ q := hp.two_le.trans (le_self_pow hp.one_le (by omega))
  have hqne : q ≠ 0 := by omega
  have hne1 : q - 1 ≠ 0 := by omega
  have hne2 : q + 1 ≠ 0 := by omega
  have hq2m1 : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    zify [Nat.one_le_pow 2 q (by omega), (by omega : 1 ≤ q)]
    ring
  have h3q : q.factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd (by
    intro hdvd
    rw [Nat.dvd_iff_mod_eq_zero] at hdvd
    omega)
  have h3q1 : (q + 1).factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd (by
    intro hdvd
    rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, hqmod] at hdvd
    norm_num at hdvd)
  rw [hcard, hq2m1, Nat.factorization_mul hqne (mul_ne_zero hne1 hne2),
    Nat.factorization_mul hne1 hne2, Finsupp.add_apply, h3q, Finsupp.add_apply, h3q1]
  simp

theorem factorization_three_card_statedSU_eq_two_mul {n p f : ℕ} (hn : n = 4 ∨ n = 5)
    (hp : p.Prime) (hf : 1 ≤ f) (hq : p ^ f % 3 = 1) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 2) :
    (Nat.card (StatedSU n (p ^ f) K)).factorization 3 =
      2 * (Nat.card (StatedSU 2 (p ^ f) K)).factorization 3 := by
  have h : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq2 : 2 ≤ p ^ f := hp.two_le.trans (le_self_pow hp.one_le (by omega))
  rcases hn with rfl | rfl
  · rw [nat_card_statedSU_four h, factorization_three_prod_four hq2 hq,
      factorization_three_card_statedSU_two hp hf hq hK]
  · rw [nat_card_statedSU_five h, factorization_three_prod_five hq2 hq,
      factorization_three_card_statedSU_two hp hf hq hK]
theorem exists_fixed_pair_norm_neg_one_statedSU {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 2) (φ : RingAut K)
    (hφ : ∀ x : K, φ x = x ^ ((p ^ (f / 3 ^ (f.factorization 3))) ^ 2)) :
    ∃ c c' : K, c ≠ c' ∧ c ^ (p ^ f + 1) = -1 ∧ c' ^ (p ^ f + 1) = -1 ∧ φ c = c ∧ φ c' = c' := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have hK' : Nat.card K = p ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K p :=
    charP_of_card_eq_prime_pow (f := 2 * f) (by rwa [Nat.card_eq_fintype_card] at hK')
  set b : ℕ := f.factorization 3 with hb
  set f0 : ℕ := f / 3 ^ b with hf0
  set q0 : ℕ := p ^ f0 with hq0
  set q : ℕ := p ^ f with hq
  set N : ℕ := q0 ^ 2 - 1 with hN
  have h3dvd : 3 ^ b ∣ f := by
    rw [hb]
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three (by omega : f ≠ 0)).mpr le_rfl
  have hb_mul : 3 ^ b * f0 = f := by
    rw [hf0]
    exact Nat.mul_div_cancel' h3dvd
  have hf0pos : 0 < f0 := by
    by_contra h
    rw [Nat.not_lt, Nat.le_zero] at h
    rw [h, mul_zero] at hb_mul
    omega
  have hq0ge2 : 2 ≤ q0 := by
    rw [hq0]
    calc 2 ≤ p := hp.two_le
      _ ≤ p ^ f0 := le_self_pow hp.one_le (by omega)
  have hqge2 : 2 ≤ q := by
    rw [hq]
    calc 2 ≤ p := hp.two_le
      _ ≤ p ^ f := le_self_pow hp.one_le (by omega)
  have hqeq : q0 ^ (3 ^ b) = q := by
    rw [hq0, hq, ← pow_mul]
    congr 1
    rw [mul_comm, hb_mul]
  have hNpos : 0 < N := by
    rw [hN]
    have : 4 ≤ q0 ^ 2 := by nlinarith
    omega
  have hNne : N ≠ 0 := by omega
  have hq2eq : q ^ 2 = (q0 ^ 2) ^ (3 ^ b) := by
    calc q ^ 2 = (q0 ^ (3 ^ b)) ^ 2 := by rw [← hqeq]
      _ = q0 ^ ((3 ^ b) * 2) := by rw [pow_mul]
      _ = q0 ^ (2 * (3 ^ b)) := by ring_nf
      _ = (q0 ^ 2) ^ (3 ^ b) := by rw [pow_mul]
  have hNdvd : N ∣ q ^ 2 - 1 := by
    rw [hN, hq2eq]
    exact Nat.sub_one_dvd_pow_sub_one (q0 ^ 2) (3 ^ b)
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  have hgord : orderOf g = q ^ 2 - 1 := by
    rw [hg, Nat.card_units, hK, hq]
  have hgne : orderOf g ≠ 0 := by
    rw [hgord]
    have : 1 < q ^ 2 := by nlinarith
    omega
  let h : Kˣ := g ^ (orderOf g / N)
  have hhord : orderOf h = N := by
    dsimp only [h]
    exact orderOf_pow_orderOf_div hgne (by rw [hgord]; exact hNdvd)
  have hhN : h ^ N = 1 := by rw [← hhord]; exact pow_orderOf_eq_one h
  have hfix : h ^ (q0 ^ 2) = h := by
    rw [show q0 ^ 2 = N + 1 by omega, pow_succ, hhN, one_mul]
  have hhKN : (h : K) ^ N = 1 := by
    rw [← Units.val_pow_eq_pow_val, hhN, Units.val_one]
  have hfixK : (h : K) ^ (q0 ^ 2) = (h : K) := by
    rw [← Units.val_pow_eq_pow_val, hfix]
  have hfixpowK : ∀ k : ℕ, ((h : K) ^ k) ^ (q0 ^ 2) = (h : K) ^ k := by
    intro k
    rw [← pow_mul, mul_comm, pow_mul, hfixK]
  have hphipow : ∀ k : ℕ, φ ((h : K) ^ k) = (h : K) ^ k := by
    intro k
    rw [hφ, hfixpowK k]
  let u : K := (h : K) ^ (q0 - 1)
  have hupow : u ^ (q0 + 1) = 1 := by
    dsimp only [u]
    rw [← pow_mul, show (q0 - 1) * (q0 + 1) = N by
      rw [hN]
      zify [(by omega : 1 ≤ q0), (by nlinarith : 1 ≤ q0 ^ 2)]
      ring, hhKN]
  have hune : u ≠ 1 := by
    intro hu
    have h1 : h ^ (q0 - 1) = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      exact hu
    have hdvd : orderOf h ∣ q0 - 1 := orderOf_dvd_iff_pow_eq_one.mpr h1
    rw [hhord, hN] at hdvd
    have hle : q0 ^ 2 - 1 ≤ q0 - 1 := Nat.le_of_dvd (by omega) hdvd
    have hfac : q0 ^ 2 - 1 = (q0 - 1) * (q0 + 1) := by
      zify [(by omega : 1 ≤ q0), (by nlinarith : 1 ≤ q0 ^ 2)]
      ring
    have hlt : q0 - 1 < q0 ^ 2 - 1 := by
      rw [hfac]
      calc q0 - 1 = (q0 - 1) * 1 := (mul_one _).symm
        _ < (q0 - 1) * (q0 + 1) := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
    omega
  have huphi : φ u = u := by
    dsimp only [u]
    exact hphipow (q0 - 1)
  have hpow_q_eq : ∀ x : K, φ x = x → x ^ q = x ^ q0 := by
    intro x hx
    have hx2 : x ^ (q0 ^ 2) = x := by
      have h := hφ x
      rw [hx] at h
      exact h.symm
    have h3odd : Odd (3 ^ b) := (show Odd (3 : ℕ) by decide).pow
    obtain ⟨m, hm⟩ := h3odd
    have hx2m : ∀ k : ℕ, x ^ ((q0 ^ 2) ^ k) = x := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          rw [pow_succ, pow_mul, ih, hx2]
    calc x ^ q = x ^ (q0 ^ (3 ^ b)) := by rw [hqeq]
      _ = x ^ (q0 ^ (2 * m + 1)) := by rw [hm]
      _ = x ^ (q0 ^ (2 * m) * q0) := by rw [pow_succ]
      _ = (x ^ (q0 ^ (2 * m))) ^ q0 := by rw [pow_mul]
      _ = (x ^ ((q0 ^ 2) ^ m)) ^ q0 := by rw [pow_mul]
      _ = x ^ q0 := by rw [hx2m m]
  have hpow_qp1 : ∀ x : K, φ x = x → x ^ (q + 1) = x ^ (q0 + 1) := by
    intro x hx
    rw [pow_succ, show x ^ (q0 + 1) = x ^ q0 * x from pow_succ x q0, hpow_q_eq x hx]
  by_cases hpar : q0 % 2 = 1
  · have hodd : Odd q0 := Nat.odd_iff.mpr hpar
    obtain ⟨t, ht⟩ := hodd
    have h2dvd : 2 ∣ q0 - 1 := ⟨t, by omega⟩
    let c0 : K := (h : K) ^ ((q0 - 1) / 2)
    have hc0sq : c0 ^ 2 = u := by
      dsimp only [c0, u]
      rw [← pow_mul]
      congr 1
      rw [mul_comm, Nat.mul_div_cancel' h2dvd]
    have hc0sqsq : (c0 ^ (q0 + 1)) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hc0sq, hupow]
    have hc0ne1 : c0 ^ (q0 + 1) ≠ 1 := by
      intro hcone
      have h1 : (h : K) ^ (((q0 - 1) / 2) * (q0 + 1)) = 1 := by
        have hh := hcone
        dsimp only [c0] at hh
        rwa [← pow_mul] at hh
      have h1u : h ^ (((q0 - 1) / 2) * (q0 + 1)) = 1 := by
        apply Units.ext
        rw [Units.val_pow_eq_pow_val, Units.val_one]
        exact h1
      have h2 : orderOf h ∣ ((q0 - 1) / 2) * (q0 + 1) :=
        orderOf_dvd_iff_pow_eq_one.mpr h1u
      rw [hhord] at h2
      have hkpos : 0 < ((q0 - 1) / 2) * (q0 + 1) := by
        have : 1 ≤ (q0 - 1) / 2 := by omega
        positivity
      have h2k : 2 * (((q0 - 1) / 2) * (q0 + 1)) = N := by
        rw [hN, ← Nat.mul_assoc, Nat.mul_div_cancel' h2dvd]
        zify [(by omega : 1 ≤ q0), (by nlinarith : 1 ≤ q0 ^ 2)]
        ring
      have hle : N ≤ ((q0 - 1) / 2) * (q0 + 1) := Nat.le_of_dvd hkpos h2
      omega
    have hc0pow : c0 ^ (q0 + 1) = -1 := by
      rcases sq_eq_one_iff.mp hc0sqsq with h1 | h1
      · exact absurd h1 hc0ne1
      · exact h1
    have hc0phi : φ c0 = c0 := by
      dsimp only [c0]
      exact hphipow _
    have hc0ne0 : c0 ≠ 0 := by
      intro h0
      rw [h0, zero_pow (by omega : q0 + 1 ≠ 0)] at hc0pow
      exact (neg_ne_zero.mpr one_ne_zero) hc0pow.symm
    have hcuphi : φ (c0 * u) = c0 * u := by rw [map_mul, hc0phi, huphi]
    refine ⟨c0, c0 * u, ?_, ?_, ?_, hc0phi, hcuphi⟩
    · intro hcc
      have hu1 : u = 1 := by
        apply mul_left_cancel₀ hc0ne0
        rw [mul_one]
        exact hcc.symm
      exact hune hu1
    · rw [hpow_qp1 c0 hc0phi, hc0pow]
    · rw [hpow_qp1 (c0 * u) hcuphi, mul_pow, hc0pow, hupow, mul_one]
  · have hq0mod : q0 % 2 = 0 := by omega
    have heven : Even q0 := Nat.even_iff.mpr hq0mod
    have hp2 : p = 2 := by
      rcases hp.eq_two_or_odd with h2 | hodd
      · exact h2
      · exfalso
        have hodd' : Odd q0 := by rw [hq0]; exact (Nat.odd_iff.mpr hodd).pow
        exact (Nat.not_odd_iff_even.mpr heven) hodd'
    have h2K : (2 : K) = 0 := by
      have h := CharP.cast_eq_zero K p
      rwa [hp2] at h
    have hneg1 : (-1 : K) = 1 := by
      have h : (1 : K) + 1 = 0 := by rw [one_add_one_eq_two, h2K]
      calc (-1 : K) = -1 + 0 := (add_zero _).symm
        _ = -1 + (1 + 1) := by rw [h]
        _ = 1 := by ring
    let c0 : K := 1
    have hc0pow : c0 ^ (q0 + 1) = -1 := by
      dsimp only [c0]
      rw [one_pow, hneg1]
    have hc0phi : φ c0 = c0 := by
      dsimp only [c0]
      simp
    have hcuphi : φ (c0 * u) = c0 * u := by rw [map_mul, hc0phi, huphi]
    refine ⟨c0, c0 * u, ?_, ?_, ?_, hc0phi, hcuphi⟩
    · intro hcc
      have hu1 : u = 1 := by
        have h := hcc
        dsimp only [c0] at h
        simpa using h.symm
      exact hune hu1
    · rw [hpow_qp1 c0 hc0phi, hc0pow]
    · rw [hpow_qp1 (c0 * u) hcuphi, mul_pow, hc0pow, hupow, mul_one]

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
