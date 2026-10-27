module

public import CFSG.RankThree.PartTwo.Sec13.K135GL12Core
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20LieOrd

public section

namespace CFSG.RankThree.PartTwo.Sec13.K135GL12

open CFSG.Open TauCeti CFSG.HardMathSupport.Solomon.Coordinator.I1420

@[expose] def gl12Primes : List ℕ := [2, 3, 5, 7, 11, 13, 23, 41, 61, 73, 757, 1093, 3851]

theorem prime_mem_gl12Primes {p : ℕ} (hp : p.Prime) (h : p ∣ gl12Order) : p ∈ gl12Primes := by
  have hmem : p ∈ gl12Order.primeFactorsList :=
    (Nat.mem_primeFactorsList (by norm_num [gl12Order])).2 ⟨hp, h⟩
  have hsub : ∀ x ∈ gl12Order.primeFactorsList, x ∈ gl12Primes := by
    unfold gl12Order gl12Primes
    simp only [Nat.primeFactorsList_ofNat]
    decide
  exact hsub p hmem

theorem prime_pow_dvd_gl12 {p m : ℕ} (hp : p.Prime) (hm : 1 ≤ m) (h : p ^ m ∣ gl12Order) :
    p ∈ gl12Primes ∧ m ≤ 66 := by
  have hpF : p ∣ gl12Order := (dvd_pow_self p (by omega)).trans h
  have hmem := prime_mem_gl12Primes hp hpF
  refine ⟨hmem, ?_⟩
  have hlt : m < 240 := by
    by_contra hge
    push Not at hge
    have h1 : 2 ^ 240 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hge
    have h2 : 2 ^ m ≤ p ^ m := Nat.pow_le_pow_left hp.two_le _
    have h3 : p ^ m ≤ gl12Order := Nat.le_of_dvd (by norm_num [gl12Order]) h
    have h4 : gl12Order < 2 ^ 240 := by norm_num [gl12Order]
    omega
  have key : ∀ p ∈ gl12Primes, ∀ m < 240, p ^ m ∣ gl12Order → m ≤ 66 := by
    unfold gl12Primes gl12Order
    decide +kernel
  exact key p hmem m hlt h

section

open Finset

@[expose] def survA : List (ℕ × ℕ × ℕ) :=
  [(1, 2, 3), (1, 2, 6), (1, 3, 3), (1, 3, 4), (1, 3, 5), (1, 3, 6), (1, 5, 2), (1, 7, 1), (1, 7, 2),
   (1, 11, 1), (1, 11, 2), (1, 13, 1), (1, 23, 1), (1, 41, 1), (2, 2, 2), (2, 2, 3), (2, 3, 1),
   (2, 3, 2), (2, 3, 3), (2, 3, 4), (2, 13, 1), (3, 3, 1), (3, 3, 2), (3, 3, 3), (4, 3, 1), (4, 3, 2),
   (5, 3, 1), (5, 3, 2), (6, 3, 1), (7, 3, 1), (8, 3, 1), (9, 3, 1), (10, 3, 1), (11, 3, 1)]

@[expose] def survTA : List (ℕ × ℕ × ℕ) :=
  [(2, 2, 2), (2, 3, 1), (2, 3, 2), (2, 5, 1), (3, 2, 1), (3, 3, 1), (3, 3, 2), (4, 2, 1), (4, 3, 1),
   (5, 2, 1), (5, 3, 1)]

private theorem gl12kA_two_le_pow {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) : 2 ≤ p ^ f := by
  have h1 : p ^ 1 ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf
  have h2 := hp.two_le
  rw [pow_one] at h1
  omega

private theorem gl12kA_pow_dvd {p f e G N R : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (he : 1 ≤ e)
    (hG : Nat.Coprime (p ^ f) G) (hmul : G * N = (p ^ f) ^ e * R) (hN : N ∣ gl12Order) :
    p ∈ gl12Primes ∧ f * e ≤ 66 := by
  have h1 : (p ^ f) ^ e ∣ G * gl12Order :=
    (Dvd.intro R hmul.symm).trans (mul_dvd_mul_left G hN)
  have h2 : (p ^ f) ^ e ∣ gl12Order := (Nat.Coprime.pow_left e hG).dvd_of_dvd_mul_left h1
  have h3 : p ^ (f * e) ∣ gl12Order := by
    rw [pow_mul]
    exact h2
  exact prime_pow_dvd_gl12 hp (by nlinarith) h3

private theorem gl12kA_bounds {n f : ℕ} (hn : 1 ≤ n) (hf : 1 ≤ f)
    (hfN : f * (n * (n + 1) / 2) ≤ 66) : n < 12 ∧ f < 67 := by
  have he1 : 1 ≤ n * (n + 1) / 2 := Nat.div_pos (by nlinarith) (by norm_num)
  have h1 : f * 1 ≤ f * (n * (n + 1) / 2) := Nat.mul_le_mul (le_refl f) he1
  have h2 : 1 * (n * (n + 1) / 2) ≤ f * (n * (n + 1) / 2) := Nat.mul_le_mul hf (le_refl _)
  have hN66 : n * (n + 1) / 2 ≤ 66 := by omega
  refine ⟨?_, by omega⟩
  by_contra hc
  push Not at hc
  have h78 : 78 ≤ n * (n + 1) / 2 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by nlinarith)
  omega

set_option synthInstance.maxSize 100000 in
private theorem gl12kA_gridA :
    ∀ n < 12, ∀ p ∈ gl12Primes, ∀ f < 67, 1 ≤ n → 1 ≤ f → f * (n * (n + 1) / 2) ≤ 66 →
      (n = 1 → 4 ≤ p ^ f) →
      ¬ ((n = 1 ∧ (p ^ f = 4 ∨ p ^ f = 5 ∨ p ^ f = 9)) ∨ (n = 2 ∧ p ^ f = 2) ∨
        (n = 3 ∧ p ^ f = 2)) →
      orderA n (p ^ f) ∣ gl12Order → (n, p, f) ∈ survA := by
  decide +kernel

private theorem gl12kA_A_reduce {n p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hn : 1 ≤ n)
    (h : orderA n (p ^ f) ∣ gl12Order) :
    p ∈ gl12Primes ∧ f * (n * (n + 1) / 2) ≤ 66 ∧ n < 12 ∧ f < 67 := by
  have hq2 : 2 ≤ p ^ f := gl12kA_two_le_pow hp hf
  have hmem : 2 ∈ Icc 2 (n + 1) := Finset.mem_Icc.2 ⟨le_refl 2, by omega⟩
  have hGd : Nat.gcd (n + 1) (p ^ f - 1) ∣ (p ^ f) ^ (n * (n + 1) / 2) *
      ∏ i ∈ Icc 2 (n + 1), ((p ^ f) ^ i - 1) :=
    Dvd.dvd.mul_left (((Nat.gcd_dvd_right (n + 1) (p ^ f - 1)).trans
      (sub_one_dvd_sq_sub_one (p ^ f))).trans
      (Finset.dvd_prod_of_mem (fun i => (p ^ f) ^ i - 1) hmem)) _
  have hmul : Nat.gcd (n + 1) (p ^ f - 1) * orderA n (p ^ f) =
      (p ^ f) ^ (n * (n + 1) / 2) * ∏ i ∈ Icc 2 (n + 1), ((p ^ f) ^ i - 1) :=
    Nat.mul_div_cancel' hGd
  have he1 : 1 ≤ n * (n + 1) / 2 := Nat.div_pos (by nlinarith) (by norm_num)
  obtain ⟨hpS, hfN⟩ := gl12kA_pow_dvd hp hf he1
    (coprime_of_dvd_sub_one hq2 (Nat.gcd_dvd_right (n + 1) (p ^ f - 1))) hmul h
  obtain ⟨hn12, hf67⟩ := gl12kA_bounds hn hf hfN
  exact ⟨hpS, hfN, hn12, hf67⟩

set_option synthInstance.maxSize 100000 in
private theorem gl12kA_gridTA :
    ∀ n < 12, ∀ p ∈ gl12Primes, ∀ f < 67, 2 ≤ n → 1 ≤ f → f * (n * (n + 1) / 2) ≤ 66 →
      (n = 2 → 3 ≤ p ^ f) → orderTwistedA n (p ^ f) ∣ gl12Order → (n, p, f) ∈ survTA := by
  decide +kernel

private theorem gl12kA_TA_reduce {n p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hn : 2 ≤ n)
    (h : orderTwistedA n (p ^ f) ∣ gl12Order) :
    p ∈ gl12Primes ∧ f * (n * (n + 1) / 2) ≤ 66 ∧ n < 12 ∧ f < 67 := by
  have hq2 : 2 ≤ p ^ f := gl12kA_two_le_pow hp hf
  have hmem : 2 ∈ Icc 2 (n + 1) := Finset.mem_Icc.2 ⟨le_refl 2, by omega⟩
  have hfac : p ^ f + 1 ∣ (fun i => if Even i then (p ^ f) ^ i - 1 else (p ^ f) ^ i + 1) 2 := by
    show p ^ f + 1 ∣ (if Even 2 then (p ^ f) ^ 2 - 1 else (p ^ f) ^ 2 + 1)
    simpa using add_one_dvd_sq_sub_one (p ^ f) (by omega)
  have hGd : Nat.gcd (n + 1) (p ^ f + 1) ∣ (p ^ f) ^ (n * (n + 1) / 2) *
      ∏ i ∈ Icc 2 (n + 1), (if Even i then (p ^ f) ^ i - 1 else (p ^ f) ^ i + 1) :=
    Dvd.dvd.mul_left (((Nat.gcd_dvd_right (n + 1) (p ^ f + 1)).trans hfac).trans
      (Finset.dvd_prod_of_mem (fun i => if Even i then (p ^ f) ^ i - 1 else (p ^ f) ^ i + 1)
        hmem)) _
  have hmul : Nat.gcd (n + 1) (p ^ f + 1) * orderTwistedA n (p ^ f) =
      (p ^ f) ^ (n * (n + 1) / 2) *
        ∏ i ∈ Icc 2 (n + 1), (if Even i then (p ^ f) ^ i - 1 else (p ^ f) ^ i + 1) :=
    Nat.mul_div_cancel' hGd
  have he1 : 1 ≤ n * (n + 1) / 2 := Nat.div_pos (by nlinarith) (by norm_num)
  obtain ⟨hpS, hfN⟩ := gl12kA_pow_dvd hp hf he1
    (coprime_of_dvd_add_one (Nat.gcd_dvd_right (n + 1) (p ^ f + 1))) hmul h
  obtain ⟨hn12, hf67⟩ := gl12kA_bounds (by omega) hf hfN
  exact ⟨hpS, hfN, hn12, hf67⟩

theorem census_A {n : ℕ} {q : PrimePower} (hv : (LieTypeIndex.A n q).Valid)
    (h : orderA n q.card ∣ gl12Order) : (n, q.p, q.exponent) ∈ survA := by
  have hv' := (LieTypeIndex.valid_iff (LieTypeIndex.A n q)).1 hv
  have hr : 1 ≤ n ∧ (n = 1 → 4 ≤ q.card) :=
    (LieTypeIndex.inStandardRange_iff (LieTypeIndex.A n q)).1 hv'.1
  have hd : ¬ ((n = 1 ∧ (q.card = 4 ∨ q.card = 5 ∨ q.card = 9)) ∨ (n = 2 ∧ q.card = 2) ∨
      (n = 3 ∧ q.card = 2)) :=
    fun h' => hv'.2 ((LieTypeIndex.isDuplicateRepresentative_iff (LieTypeIndex.A n q)).2 h')
  rw [PrimePower.card_def] at h hr hd
  obtain ⟨hn, hn4⟩ := hr
  have hf : 1 ≤ q.exponent := by
    have := q.exponent_pos
    omega
  obtain ⟨hpS, hfN, hn12, hf67⟩ :=
    gl12kA_A_reduce (n := n) (p := q.p) (f := q.exponent) q.prime_p hf hn h
  exact gl12kA_gridA n hn12 q.p hpS q.exponent hf67 hn hf hfN hn4 hd h

theorem census_twistedA {n : ℕ} {q : PrimePower} (hv : (LieTypeIndex.twistedA n q).Valid)
    (h : orderTwistedA n q.card ∣ gl12Order) : (n, q.p, q.exponent) ∈ survTA := by
  have hv' := (LieTypeIndex.valid_iff (LieTypeIndex.twistedA n q)).1 hv
  have hr : 2 ≤ n ∧ (n = 2 → 3 ≤ q.card) :=
    (LieTypeIndex.inStandardRange_iff (LieTypeIndex.twistedA n q)).1 hv'.1
  rw [PrimePower.card_def] at h hr
  obtain ⟨hn, hn3⟩ := hr
  have hf : 1 ≤ q.exponent := by
    have := q.exponent_pos
    omega
  obtain ⟨hpS, hfN, hn12, hf67⟩ :=
    gl12kA_TA_reduce (n := n) (p := q.p) (f := q.exponent) q.prime_p hf hn h
  exact gl12kA_gridTA n hn12 q.p hpS q.exponent hf67 hn hf hfN hn3 h

end

section

@[expose] def survB : List (ℕ × ℕ × ℕ) :=
  [(2, 2, 3), (2, 3, 2), (2, 3, 3), (2, 11, 1), (3, 2, 1), (3, 3, 1), (3, 3, 2), (4, 3, 1), (5, 3, 1),
   (6, 3, 1)]

@[expose] def survC : List (ℕ × ℕ × ℕ) := [(3, 3, 1), (3, 3, 2), (4, 3, 1), (5, 3, 1), (6, 3, 1)]

@[expose] def survD : List (ℕ × ℕ × ℕ) := [(4, 2, 1), (4, 3, 1), (5, 3, 1), (6, 3, 1), (7, 3, 1)]

@[expose] def survTD : List (ℕ × ℕ × ℕ) := [(4, 3, 1), (5, 3, 1), (6, 3, 1)]

set_option synthInstance.maxSize 20000 in
private theorem gl12kB_gridB : ∀ n < 9, ∀ p ∈ gl12Primes, ∀ f ≤ 66, 0 < f → 2 ≤ n →
    f * (n * n) ≤ 66 → ¬(n = 2 ∧ p ^ f = 2) → ¬(n = 2 ∧ p ^ f = 3) →
    orderBC n (p ^ f) ∣ gl12Order → (n, p, f) ∈ survB := by
  decide +kernel

set_option synthInstance.maxSize 20000 in
private theorem gl12kB_gridC : ∀ n < 9, ∀ p ∈ gl12Primes, ∀ f ≤ 66, 0 < f → 3 ≤ n → p ≠ 2 →
    f * (n * n) ≤ 66 → orderBC n (p ^ f) ∣ gl12Order → (n, p, f) ∈ survC := by
  decide +kernel

set_option synthInstance.maxSize 20000 in
private theorem gl12kB_gridD : ∀ n < 9, ∀ p ∈ gl12Primes, ∀ f ≤ 66, 0 < f → 4 ≤ n →
    f * (n * (n - 1)) ≤ 66 → orderD n (p ^ f) ∣ gl12Order → (n, p, f) ∈ survD := by
  decide +kernel

set_option synthInstance.maxSize 20000 in
private theorem gl12kB_gridTD : ∀ n < 9, ∀ p ∈ gl12Primes, ∀ f ≤ 66, 0 < f → 4 ≤ n →
    f * (n * (n - 1)) ≤ 66 → orderTwistedD n (p ^ f) ∣ gl12Order → (n, p, f) ∈ survTD := by
  decide +kernel

private theorem gl12kB_pow_dvd {N G Q e R : ℕ} (hG : Nat.Coprime Q G) (hmul : G * N = Q ^ e * R)
    (hN : N ∣ gl12Order) : Q ^ e ∣ gl12Order := by
  have h1 : Q ^ e ∣ G * gl12Order := (Dvd.intro R hmul.symm).trans (mul_dvd_mul_left G hN)
  exact (Nat.Coprime.pow_left e hG).dvd_of_dvd_mul_left h1

private theorem gl12kB_prime_bound {p f e : ℕ} (hp : p.Prime) (hf : 0 < f) (he : 0 < e)
    (h : (p ^ f) ^ e ∣ gl12Order) : p ∈ gl12Primes ∧ f * e ≤ 66 := by
  rw [← pow_mul] at h
  have hfe : 0 < f * e := Nat.mul_pos hf he
  exact prime_pow_dvd_gl12 hp (by omega) h

private theorem gl12kB_fe_bound {f e : ℕ} (hf : 0 < f) (he : 0 < e) (hfe : f * e ≤ 66) :
    e ≤ 66 ∧ f ≤ 66 := by
  have h1 : e ≤ f * e := Nat.le_mul_of_pos_left e hf
  have h2 : f ≤ f * e := Nat.le_mul_of_pos_right f he
  omega

private theorem gl12kB_B {Q n : ℕ} (hQ : 2 ≤ Q) (hn : 2 ≤ n) (h : orderBC n Q ∣ gl12Order) :
    Q ^ (n * n) ∣ gl12Order := by
  have hmem : 1 ∈ Finset.Icc 1 n := Finset.mem_Icc.2 ⟨le_rfl, by omega⟩
  have hfac : Q - 1 ∣ (fun i => Q ^ (2 * i) - 1) 1 := by
    show Q - 1 ∣ Q ^ (2 * 1) - 1
    exact Nat.sub_one_dvd_pow_sub_one Q (2 * 1)
  have hGd : Nat.gcd 2 (Q - 1) ∣ Q ^ (n * n) * ∏ i ∈ Finset.Icc 1 n, (Q ^ (2 * i) - 1) :=
    Dvd.dvd.mul_left (((Nat.gcd_dvd_right 2 (Q - 1)).trans hfac).trans
      (Finset.dvd_prod_of_mem (fun i => Q ^ (2 * i) - 1) hmem)) _
  have hmul : Nat.gcd 2 (Q - 1) * orderBC n Q =
      Q ^ (n * n) * ∏ i ∈ Finset.Icc 1 n, (Q ^ (2 * i) - 1) :=
    Nat.mul_div_cancel' hGd
  exact gl12kB_pow_dvd (coprime_of_dvd_sub_one hQ (Nat.gcd_dvd_right 2 (Q - 1))) hmul h

private theorem gl12kB_D {Q n : ℕ} (hQ : 2 ≤ Q) (hn : 4 ≤ n) (h : orderD n Q ∣ gl12Order) :
    Q ^ (n * (n - 1)) ∣ gl12Order := by
  have hGd : Nat.gcd 4 (Q ^ n - 1) ∣ Q ^ (n * (n - 1)) * ((Q ^ n - 1) *
      ∏ i ∈ Finset.Icc 1 (n - 1), (Q ^ (2 * i) - 1)) :=
    Dvd.dvd.mul_left (Dvd.dvd.mul_right (Nat.gcd_dvd_right 4 (Q ^ n - 1)) _) _
  have hmul : Nat.gcd 4 (Q ^ n - 1) * orderD n Q = Q ^ (n * (n - 1)) * ((Q ^ n - 1) *
      ∏ i ∈ Finset.Icc 1 (n - 1), (Q ^ (2 * i) - 1)) := by
    have h1 : Q ^ (n * (n - 1)) * (Q ^ n - 1) * ∏ i ∈ Finset.Icc 1 (n - 1), (Q ^ (2 * i) - 1) =
        Q ^ (n * (n - 1)) * ((Q ^ n - 1) * ∏ i ∈ Finset.Icc 1 (n - 1), (Q ^ (2 * i) - 1)) := by
      ring
    unfold orderD
    rw [h1]
    exact Nat.mul_div_cancel' hGd
  exact gl12kB_pow_dvd (coprime_of_dvd_pow_sub_one hQ (show 1 ≤ n by omega)
    (Nat.gcd_dvd_right 4 (Q ^ n - 1))) hmul h

private theorem gl12kB_TD {Q n : ℕ} (hn : 4 ≤ n) (h : orderTwistedD n Q ∣ gl12Order) :
    Q ^ (n * (n - 1)) ∣ gl12Order := by
  have hGd : Nat.gcd 4 (Q ^ n + 1) ∣ Q ^ (n * (n - 1)) * ((Q ^ n + 1) *
      ∏ i ∈ Finset.Icc 1 (n - 1), (Q ^ (2 * i) - 1)) :=
    Dvd.dvd.mul_left (Dvd.dvd.mul_right (Nat.gcd_dvd_right 4 (Q ^ n + 1)) _) _
  have hmul : Nat.gcd 4 (Q ^ n + 1) * orderTwistedD n Q = Q ^ (n * (n - 1)) * ((Q ^ n + 1) *
      ∏ i ∈ Finset.Icc 1 (n - 1), (Q ^ (2 * i) - 1)) := by
    have h1 : Q ^ (n * (n - 1)) * (Q ^ n + 1) * ∏ i ∈ Finset.Icc 1 (n - 1), (Q ^ (2 * i) - 1) =
        Q ^ (n * (n - 1)) * ((Q ^ n + 1) * ∏ i ∈ Finset.Icc 1 (n - 1), (Q ^ (2 * i) - 1)) := by
      ring
    unfold orderTwistedD
    rw [h1]
    exact Nat.mul_div_cancel' hGd
  exact gl12kB_pow_dvd (coprime_of_dvd_pow_add_one (show 1 ≤ n by omega)
    (Nat.gcd_dvd_right 4 (Q ^ n + 1))) hmul h

theorem census_B {n : ℕ} {q : PrimePower} (hv : (LieTypeIndex.B n q).Valid)
    (h : orderBC n q.card ∣ gl12Order) : (n, q.p, q.exponent) ∈ survB := by
  have hv' := (LieTypeIndex.valid_iff _).1 hv
  have hr : 2 ≤ n ∧ ¬(n = 2 ∧ q.card = 2) := (LieTypeIndex.inStandardRange_iff _).1 hv'.1
  have hd : ¬(n = 2 ∧ q.card = 3) :=
    fun h' => hv'.2 ((LieTypeIndex.isDuplicateRepresentative_iff _).2 h')
  have hn : 2 ≤ n := hr.1
  have hpow := gl12kB_B q.isPrimePow_card.two_le hn h
  rw [PrimePower.card_def] at hpow hr hd h
  have hn0 : 0 < n * n := Nat.mul_pos (by omega) (by omega)
  obtain ⟨hp, hfe⟩ := gl12kB_prime_bound q.prime_p q.exponent_pos hn0 hpow
  obtain ⟨he66, hf66⟩ := gl12kB_fe_bound q.exponent_pos hn0 hfe
  have hn9 : n < 9 := by
    by_contra hc
    push Not at hc
    have := Nat.mul_le_mul hc hc
    omega
  exact gl12kB_gridB n hn9 q.p hp q.exponent hf66 q.exponent_pos hn hfe hr.2 hd h

theorem census_C {n : ℕ} {q : PrimePower} (hv : (LieTypeIndex.C n q).Valid)
    (h : orderBC n q.card ∣ gl12Order) : (n, q.p, q.exponent) ∈ survC := by
  have hr : 3 ≤ n ∧ q.p ≠ 2 :=
    (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  have hn3 : 3 ≤ n := hr.1
  have hn : 2 ≤ n := by omega
  have hpow := gl12kB_B q.isPrimePow_card.two_le hn h
  rw [PrimePower.card_def] at hpow h
  have hn0 : 0 < n * n := Nat.mul_pos (by omega) (by omega)
  obtain ⟨hp, hfe⟩ := gl12kB_prime_bound q.prime_p q.exponent_pos hn0 hpow
  obtain ⟨he66, hf66⟩ := gl12kB_fe_bound q.exponent_pos hn0 hfe
  have hn9 : n < 9 := by
    by_contra hc
    push Not at hc
    have := Nat.mul_le_mul hc hc
    omega
  exact gl12kB_gridC n hn9 q.p hp q.exponent hf66 q.exponent_pos hn3 hr.2 hfe h

theorem census_D {n : ℕ} {q : PrimePower} (hv : (LieTypeIndex.D n q).Valid)
    (h : orderD n q.card ∣ gl12Order) : (n, q.p, q.exponent) ∈ survD := by
  have hn : 4 ≤ n := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  have hpow := gl12kB_D q.isPrimePow_card.two_le hn h
  rw [PrimePower.card_def] at hpow h
  have hn0 : 0 < n * (n - 1) := Nat.mul_pos (by omega) (by omega)
  obtain ⟨hp, hfe⟩ := gl12kB_prime_bound q.prime_p q.exponent_pos hn0 hpow
  obtain ⟨he66, hf66⟩ := gl12kB_fe_bound q.exponent_pos hn0 hfe
  have hn9 : n < 9 := by
    by_contra hc
    push Not at hc
    have := Nat.mul_le_mul hc (show 8 ≤ n - 1 by omega)
    omega
  exact gl12kB_gridD n hn9 q.p hp q.exponent hf66 q.exponent_pos hn hfe h

theorem census_twistedD {n : ℕ} {q : PrimePower} (hv : (LieTypeIndex.twistedD n q).Valid)
    (h : orderTwistedD n q.card ∣ gl12Order) : (n, q.p, q.exponent) ∈ survTD := by
  have hn : 4 ≤ n := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  have hpow := gl12kB_TD hn h
  rw [PrimePower.card_def] at hpow h
  have hn0 : 0 < n * (n - 1) := Nat.mul_pos (by omega) (by omega)
  obtain ⟨hp, hfe⟩ := gl12kB_prime_bound q.prime_p q.exponent_pos hn0 hpow
  obtain ⟨he66, hf66⟩ := gl12kB_fe_bound q.exponent_pos hn0 hfe
  have hn9 : n < 9 := by
    by_contra hc
    push Not at hc
    have := Nat.mul_le_mul hc (show 8 ≤ n - 1 by omega)
    omega
  exact gl12kB_gridTD n hn9 q.p hp q.exponent hf66 q.exponent_pos hn hfe h

end

section

@[expose] def survG2 : List (ℕ × ℕ) := [(2, 2), (3, 1), (3, 2)]

@[expose] def survD4t : List (ℕ × ℕ) := [(2, 1), (3, 1)]

private theorem gl12kE_sub_one_dvd (q : ℕ) : q - 1 ∣ q ^ 2 - 1 := by
  rcases Nat.eq_zero_or_pos q with h0 | hpos
  · subst h0
    norm_num
  · obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    refine ⟨n + 2, ?_⟩
    have h2 : (n + 1) ^ 2 = n * (n + 2) + 1 := by ring
    rw [h2, Nat.add_sub_cancel]

private theorem gl12kE_add_one_dvd (q : ℕ) : q + 1 ∣ q ^ 2 - 1 := by
  rcases Nat.eq_zero_or_pos q with h0 | hpos
  · subst h0
    norm_num
  · obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
    refine ⟨n, ?_⟩
    have h2 : (n + 1) ^ 2 = (n + 1 + 1) * n + 1 := by ring
    rw [h2, Nat.add_sub_cancel]

private theorem gl12kE_pow_dvd_div {q N g A : ℕ} (hg : g ∣ A) : q ^ N ∣ q ^ N * A / g := by
  rcases Nat.eq_zero_or_pos g with h0 | hpos
  · subst h0
    simp
  · obtain ⟨B, rfl⟩ := hg
    rw [mul_left_comm, Nat.mul_div_cancel_left _ hpos]
    exact dvd_mul_right _ _

private theorem gl12kE_E6_pow (q : ℕ) : q ^ 36 ∣ orderE6 q := by
  have hA : Nat.gcd 3 (q - 1) ∣ (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 - 1) *
      (q ^ 2 - 1) :=
    Dvd.dvd.mul_left ((Nat.gcd_dvd_right 3 (q - 1)).trans (gl12kE_sub_one_dvd q)) _
  have heq : orderE6 q = q ^ 36 * ((q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
      (q ^ 5 - 1) * (q ^ 2 - 1)) / Nat.gcd 3 (q - 1) := by
    unfold orderE6
    congr 1
    ring
  rw [heq]
  exact gl12kE_pow_dvd_div hA

private theorem gl12kE_E7_pow (q : ℕ) : q ^ 63 ∣ orderE7 q := by
  have hA : Nat.gcd 2 (q - 1) ∣ (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 10 - 1) *
      (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1) :=
    Dvd.dvd.mul_left ((Nat.gcd_dvd_right 2 (q - 1)).trans (gl12kE_sub_one_dvd q)) _
  have heq : orderE7 q = q ^ 63 * ((q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 10 - 1) *
      (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1)) / Nat.gcd 2 (q - 1) := by
    unfold orderE7
    congr 1
    ring
  rw [heq]
  exact gl12kE_pow_dvd_div hA

private theorem gl12kE_E8_pow (q : ℕ) : q ^ 120 ∣ orderE8 q :=
  ⟨(q ^ 30 - 1) * (q ^ 24 - 1) * (q ^ 20 - 1) * (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) *
    (q ^ 8 - 1) * (q ^ 2 - 1), by unfold orderE8; ring⟩

private theorem gl12kE_F4_pow (q : ℕ) : q ^ 24 ∣ orderF4 q :=
  ⟨(q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1), by unfold orderF4; ring⟩

private theorem gl12kE_G2_pow (q : ℕ) : q ^ 6 ∣ orderG2 q :=
  ⟨(q ^ 6 - 1) * (q ^ 2 - 1), by unfold orderG2; ring⟩

private theorem gl12kE_trialityD4_pow (q : ℕ) : q ^ 12 ∣ orderTrialityD4 q :=
  ⟨(q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1), by unfold orderTrialityD4; ring⟩

private theorem gl12kE_twistedE6_pow (q : ℕ) : q ^ 36 ∣ orderTwistedE6 q := by
  have hA : Nat.gcd 3 (q + 1) ∣ (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
      (q ^ 5 + 1) * (q ^ 2 - 1) :=
    Dvd.dvd.mul_left ((Nat.gcd_dvd_right 3 (q + 1)).trans (gl12kE_add_one_dvd q)) _
  have heq : orderTwistedE6 q = q ^ 36 * ((q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
      (q ^ 5 + 1) * (q ^ 2 - 1)) / Nat.gcd 3 (q + 1) := by
    unfold orderTwistedE6
    congr 1
    ring
  rw [heq]
  exact gl12kE_pow_dvd_div hA

private theorem gl12kE_card_pow {q : PrimePower} {e : ℕ} (he : 1 ≤ e) (hd : q.card ^ e ∣ gl12Order) :
    q.p ∈ gl12Primes ∧ q.exponent * e ≤ 66 := by
  have hf := q.exponent_pos
  have h1 : q.p ^ (q.exponent * e) ∣ gl12Order := by
    rw [PrimePower.card_def, ← pow_mul] at hd
    exact hd
  have hpos : 0 < q.exponent * e := mul_pos hf (by omega)
  exact prime_pow_dvd_gl12 q.prime_p hpos h1

theorem census_E6 {q : PrimePower} (h : orderE6 q.card ∣ gl12Order) : (q.p, q.exponent) = (3, 1) := by
  have hd : q.card ^ 36 ∣ gl12Order := (gl12kE_E6_pow q.card).trans h
  obtain ⟨hp, hb⟩ := gl12kE_card_pow (by norm_num) hd
  have grid : ∀ p ∈ gl12Primes, ∀ f ∈ List.range 67, 1 ≤ f → f * 36 ≤ 66 →
      orderE6 (p ^ f) ∣ gl12Order → p = 3 ∧ f = 1 := by
    unfold orderE6 gl12Primes gl12Order
    decide +kernel
  have h' : orderE6 (q.p ^ q.exponent) ∣ gl12Order := by
    rw [← PrimePower.card_def]
    exact h
  obtain ⟨h3, h1⟩ := grid q.p hp q.exponent (List.mem_range.2 (by omega))
    (by have := q.exponent_pos; omega) hb h'
  rw [h3, h1]

theorem census_E7 {q : PrimePower} : ¬ orderE7 q.card ∣ gl12Order := by
  intro h
  have hd : q.card ^ 63 ∣ gl12Order := (gl12kE_E7_pow q.card).trans h
  obtain ⟨hp, hb⟩ := gl12kE_card_pow (by norm_num) hd
  have grid : ∀ p ∈ gl12Primes, ∀ f ∈ List.range 67, 1 ≤ f → f * 63 ≤ 66 →
      ¬ orderE7 (p ^ f) ∣ gl12Order := by
    unfold orderE7 gl12Primes gl12Order
    decide +kernel
  have h' : orderE7 (q.p ^ q.exponent) ∣ gl12Order := by
    rw [← PrimePower.card_def]
    exact h
  exact grid q.p hp q.exponent (List.mem_range.2 (by omega))
    (by have := q.exponent_pos; omega) hb h'

theorem census_E8 {q : PrimePower} : ¬ orderE8 q.card ∣ gl12Order := by
  intro h
  have hd : q.card ^ 120 ∣ gl12Order := (gl12kE_E8_pow q.card).trans h
  obtain ⟨-, hb⟩ := gl12kE_card_pow (by norm_num) hd
  have := q.exponent_pos
  omega

theorem census_F4 {q : PrimePower} (h : orderF4 q.card ∣ gl12Order) : (q.p, q.exponent) = (3, 1) := by
  have hd : q.card ^ 24 ∣ gl12Order := (gl12kE_F4_pow q.card).trans h
  obtain ⟨hp, hb⟩ := gl12kE_card_pow (by norm_num) hd
  have grid : ∀ p ∈ gl12Primes, ∀ f ∈ List.range 67, 1 ≤ f → f * 24 ≤ 66 →
      orderF4 (p ^ f) ∣ gl12Order → p = 3 ∧ f = 1 := by
    unfold orderF4 gl12Primes gl12Order
    decide +kernel
  have h' : orderF4 (q.p ^ q.exponent) ∣ gl12Order := by
    rw [← PrimePower.card_def]
    exact h
  obtain ⟨h3, h1⟩ := grid q.p hp q.exponent (List.mem_range.2 (by omega))
    (by have := q.exponent_pos; omega) hb h'
  rw [h3, h1]

theorem census_G2 {q : PrimePower} (hv : (LieTypeIndex.G2 q).Valid) (h : orderG2 q.card ∣ gl12Order) :
    (q.p, q.exponent) ∈ survG2 := by
  have h3 : 3 ≤ q.card :=
    (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  have hd : q.card ^ 6 ∣ gl12Order := (gl12kE_G2_pow q.card).trans h
  obtain ⟨hp, hb⟩ := gl12kE_card_pow (by norm_num) hd
  have grid : ∀ p ∈ gl12Primes, ∀ f ∈ List.range 67, 1 ≤ f → f * 6 ≤ 66 → 3 ≤ p ^ f →
      orderG2 (p ^ f) ∣ gl12Order → (p, f) ∈ survG2 := by
    unfold orderG2 gl12Primes gl12Order survG2
    decide +kernel
  have h' : orderG2 (q.p ^ q.exponent) ∣ gl12Order := by
    rw [← PrimePower.card_def]
    exact h
  have h3' : 3 ≤ q.p ^ q.exponent := by
    rw [← PrimePower.card_def]
    exact h3
  exact grid q.p hp q.exponent (List.mem_range.2 (by omega))
    (by have := q.exponent_pos; omega) hb h3' h'

theorem census_twistedE6 {q : PrimePower} : ¬ orderTwistedE6 q.card ∣ gl12Order := by
  intro h
  have hd : q.card ^ 36 ∣ gl12Order := (gl12kE_twistedE6_pow q.card).trans h
  obtain ⟨hp, hb⟩ := gl12kE_card_pow (by norm_num) hd
  have grid : ∀ p ∈ gl12Primes, ∀ f ∈ List.range 67, 1 ≤ f → f * 36 ≤ 66 →
      ¬ orderTwistedE6 (p ^ f) ∣ gl12Order := by
    unfold orderTwistedE6 gl12Primes gl12Order
    decide +kernel
  have h' : orderTwistedE6 (q.p ^ q.exponent) ∣ gl12Order := by
    rw [← PrimePower.card_def]
    exact h
  exact grid q.p hp q.exponent (List.mem_range.2 (by omega))
    (by have := q.exponent_pos; omega) hb h'

theorem census_trialityD4 {q : PrimePower} (h : orderTrialityD4 q.card ∣ gl12Order) :
    (q.p, q.exponent) ∈ survD4t := by
  have hd : q.card ^ 12 ∣ gl12Order := (gl12kE_trialityD4_pow q.card).trans h
  obtain ⟨hp, hb⟩ := gl12kE_card_pow (by norm_num) hd
  have grid : ∀ p ∈ gl12Primes, ∀ f ∈ List.range 67, 1 ≤ f → f * 12 ≤ 66 →
      orderTrialityD4 (p ^ f) ∣ gl12Order → (p, f) ∈ survD4t := by
    unfold orderTrialityD4 gl12Primes gl12Order survD4t
    decide +kernel
  have h' : orderTrialityD4 (q.p ^ q.exponent) ∣ gl12Order := by
    rw [← PrimePower.card_def]
    exact h
  exact grid q.p hp q.exponent (List.mem_range.2 (by omega))
    (by have := q.exponent_pos; omega) hb h'

theorem census_suzuki {m : ℕ} (hm : 1 ≤ m) (h : orderSuzuki (2 ^ (2 * m + 1)) ∣ gl12Order) : m = 1 := by
  have hd : 2 ^ ((2 * m + 1) * 2) ∣ gl12Order := by
    refine dvd_trans ?_ h
    unfold orderSuzuki
    rw [← pow_mul (2 : ℕ) (2 * m + 1) 2]
    exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  obtain ⟨-, hb⟩ := prime_pow_dvd_gl12 Nat.prime_two (by omega) hd
  have grid : ∀ m ∈ List.range 17, 1 ≤ m → orderSuzuki (2 ^ (2 * m + 1)) ∣ gl12Order → m = 1 := by
    unfold orderSuzuki gl12Order
    decide +kernel
  exact grid m (List.mem_range.2 (by omega)) hm h

theorem census_reeG2 {m : ℕ} (hm : 1 ≤ m) : ¬ orderRee (3 ^ (2 * m + 1)) ∣ gl12Order := by
  intro h
  have hd : 3 ^ ((2 * m + 1) * 3) ∣ gl12Order := by
    refine dvd_trans ?_ h
    unfold orderRee
    rw [← pow_mul (3 : ℕ) (2 * m + 1) 3]
    exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  obtain ⟨-, hb⟩ := prime_pow_dvd_gl12 Nat.prime_three (by omega) hd
  have grid : ∀ m ∈ List.range 11, 1 ≤ m → ¬ orderRee (3 ^ (2 * m + 1)) ∣ gl12Order := by
    unfold orderRee gl12Order
    decide +kernel
  exact grid m (List.mem_range.2 (by omega)) hm h

theorem census_reeF4 {m : ℕ} (hm : 1 ≤ m) : ¬ orderTwistedF4 (2 ^ (2 * m + 1)) ∣ gl12Order := by
  intro h
  have hd : 2 ^ ((2 * m + 1) * 12) ∣ gl12Order := by
    refine dvd_trans ?_ h
    unfold orderTwistedF4
    rw [← pow_mul (2 : ℕ) (2 * m + 1) 12]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) _) _
  obtain ⟨-, hb⟩ := prime_pow_dvd_gl12 Nat.prime_two (by omega) hd
  have grid : ∀ m ∈ List.range 3, 1 ≤ m → ¬ orderTwistedF4 (2 ^ (2 * m + 1)) ∣ gl12Order := by
    unfold orderTwistedF4 gl12Order
    decide +kernel
  exact grid m (List.mem_range.2 (by omega)) hm h

end

@[expose] def GL12Surv : LieTypeIndex → Prop
  | .A n q => (n, q.p, q.exponent) ∈ survA
  | .twistedA n q => (n, q.p, q.exponent) ∈ survTA
  | .B n q => (n, q.p, q.exponent) ∈ survB
  | .C n q => (n, q.p, q.exponent) ∈ survC
  | .D n q => (n, q.p, q.exponent) ∈ survD
  | .twistedD n q => (n, q.p, q.exponent) ∈ survTD
  | .E6 q => (q.p, q.exponent) = (3, 1)
  | .E7 _ => False
  | .E8 _ => False
  | .F4 q => (q.p, q.exponent) = (3, 1)
  | .G2 q => (q.p, q.exponent) ∈ survG2
  | .twistedE6 _ => False
  | .trialityD4 q => (q.p, q.exponent) ∈ survD4t
  | .suzuki m => m = 1
  | .reeG2 _ => False
  | .reeF4 _ => False
  | .tits => True

theorem lie_census {d : LieTypeIndex} (hd : d.Valid) (h : lieOrderFormula d ∣ gl12Order) :
    GL12Surv d := by
  have hs := ((TauCeti.LieTypeIndex.valid_iff d).1 hd).1
  rw [TauCeti.LieTypeIndex.inStandardRange_iff] at hs
  cases d with
  | A n q => exact census_A hd h
  | twistedA n q => exact census_twistedA hd h
  | B n q => exact census_B hd h
  | C n q => exact census_C hd h
  | D n q => exact census_D hd h
  | twistedD n q => exact census_twistedD hd h
  | E6 q => exact census_E6 h
  | E7 q => exact absurd h census_E7
  | E8 q => exact absurd h census_E8
  | F4 q => exact census_F4 h
  | G2 q => exact census_G2 hd h
  | twistedE6 q => exact absurd h census_twistedE6
  | trialityD4 q => exact census_trialityD4 h
  | suzuki m => exact census_suzuki hs h
  | reeG2 m => exact absurd h (census_reeG2 hs)
  | reeF4 m => exact absurd h (census_reeF4 hs)
  | tits => trivial

end CFSG.RankThree.PartTwo.Sec13.K135GL12
