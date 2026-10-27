module

public import CFSG.Timmesfeld.Orders.Distinct

public section

namespace CFSG.Timmesfeld.Orders

open CFSG.Open

private theorem ppdE6_dvd_pow_sub_one_iff {r n m : ℕ} (hr : IsPrimitivePrimeDivisor r (m * n))
    (hm : 0 < m) (hn : 0 < n) (e : ℕ) : r ∣ (2 ^ n) ^ e - 1 ↔ m ∣ e := by
  rw [PrimDiv.dvd_pow_sub_one_iff hr (Nat.mul_pos hm hn), mul_comm m n]
  exact Nat.mul_dvd_mul_iff_left hn

private theorem ppdE6_not_dvd_pow {r n m : ℕ} (hr : IsPrimitivePrimeDivisor r (m * n))
    (hm : 0 < m) (hn : 0 < n) (e : ℕ) : ¬ r ∣ (2 ^ n) ^ e := by
  intro h
  have h3 := hr.prime.dvd_of_dvd_pow (hr.prime.dvd_of_dvd_pow h)
  exact hr.ne_two (Nat.mul_pos hm hn) ((Nat.prime_dvd_prime_iff_eq hr.prime Nat.prime_two).mp h3)

private theorem ppdE6_dvd_listProd {r n m : ℕ} (hr : IsPrimitivePrimeDivisor r (m * n))
    (hm : 0 < m) (hn : 0 < n) :
    ∀ es : List ℕ, r ∣ (es.map fun e => (2 ^ n) ^ e - 1).prod → ∃ e ∈ es, m ∣ e
  | [], h => by
    simp only [List.map_nil, List.prod_nil] at h
    exact absurd h hr.prime.not_dvd_one
  | e :: es, h => by
    rw [List.map_cons, List.prod_cons] at h
    rcases hr.prime.dvd_mul.mp h with h | h
    · exact ⟨e, List.mem_cons_self, (ppdE6_dvd_pow_sub_one_iff hr hm hn e).mp h⟩
    · obtain ⟨e', he', hd⟩ := ppdE6_dvd_listProd hr hm hn es h
      exact ⟨e', List.mem_cons_of_mem _ he', hd⟩

private theorem ppdE6_ordD_four_eq {f : ℕ} (hf : 0 < f) :
    ordD 4 (2 ^ f) = (2 ^ f) ^ 12 * ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 6 - 1) *
      ((2 ^ f) ^ 4 - 1) ^ 2 := by
  have hodd : Odd ((2 ^ f) ^ 4 - 1) := odd_pow_sub_one hf (by norm_num)
  have hcop : Nat.Coprime 4 ((2 ^ f) ^ 4 - 1) := by
    have h2 : Nat.Coprime 2 ((2 ^ f) ^ 4 - 1) := Nat.coprime_two_left.mpr hodd
    simpa using Nat.Coprime.pow_left 2 h2
  have hIcc : Finset.Icc 1 (4 - 1) = {1, 2, 3} := by decide
  rw [ordD, hIcc, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton, hcop.gcd_eq_one, Nat.div_one]
  norm_num
  ring

private theorem ordE6_dvd_prod (q : ℕ) :
    ordE6 q ∣ q ^ 36 * ([12, 9, 8, 6, 5, 2].map fun e => q ^ e - 1).prod := by
  have h : ordE6 q ∣ q ^ 36 * (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
      (q ^ 5 - 1) * (q ^ 2 - 1) := by
    unfold ordE6
    refine Nat.div_dvd_of_dvd ?_
    have h1 : Nat.gcd 3 (q - 1) ∣ q - 1 := Nat.gcd_dvd_right _ _
    have h2 : q - 1 ∣ q ^ 2 - 1 := Nat.sub_one_dvd_pow_sub_one q 2
    exact (h1.trans h2).trans (Dvd.intro_left _ rfl)
  refine h.trans (Eq.dvd ?_)
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  ring

private theorem ordTwistedE6_dvd_prod {q : ℕ} (hq : 1 ≤ q) :
    ordTwistedE6 q ∣ q ^ 36 * ([12, 18, 8, 6, 10, 2].map fun e => q ^ e - 1).prod := by
  have h9 : q ^ 9 + 1 ∣ q ^ 18 - 1 := by
    have : q ^ 18 - 1 = (q ^ 9 - 1) * (q ^ 9 + 1) := by
      have h1 : 1 ≤ q ^ 9 := Nat.one_le_pow _ _ hq
      have h2 : 1 ≤ q ^ 18 := Nat.one_le_pow _ _ hq
      zify [h1, h2]
      ring
    exact Dvd.intro_left _ this.symm
  have h5 : q ^ 5 + 1 ∣ q ^ 10 - 1 := by
    have : q ^ 10 - 1 = (q ^ 5 - 1) * (q ^ 5 + 1) := by
      have h1 : 1 ≤ q ^ 5 := Nat.one_le_pow _ _ hq
      have h2 : 1 ≤ q ^ 10 := Nat.one_le_pow _ _ hq
      zify [h1, h2]
      ring
    exact Dvd.intro_left _ this.symm
  have h : ordTwistedE6 q ∣ q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
      (q ^ 5 + 1) * (q ^ 2 - 1) := by
    unfold ordTwistedE6
    refine Nat.div_dvd_of_dvd ?_
    have h1 : Nat.gcd 3 (q + 1) ∣ q + 1 := Nat.gcd_dvd_right _ _
    have h2 : q + 1 ∣ q ^ 2 - 1 := by
      have : q ^ 2 - 1 = (q - 1) * (q + 1) := by
        have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
        zify [h1, hq]
        ring
      exact Dvd.intro_left _ this.symm
    exact (h1.trans h2).trans (Dvd.intro_left _ rfl)
  refine h.trans ?_
  have := mul_dvd_mul (mul_dvd_mul (mul_dvd_mul (mul_dvd_mul (mul_dvd_mul
    (mul_dvd_mul (dvd_refl (q ^ 36)) (dvd_refl (q ^ 12 - 1))) h9) (dvd_refl (q ^ 8 - 1)))
    (dvd_refl (q ^ 6 - 1))) h5) (dvd_refl (q ^ 2 - 1))
  refine this.trans (Eq.dvd ?_)
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  ring

private theorem ppdE6_mult_contra {A B N C r : ℕ} (hN : 0 < N) (hrN : r ∣ N) (hC : ¬ r ∣ C)
    (hA : N * N ∣ A) (hAB : A ∣ B) (hB : B ∣ N * C) : False :=
  hC (hrN.trans (Nat.dvd_of_mul_dvd_mul_left hN (hA.trans (hAB.trans hB))))

theorem ordD_four_not_dvd_ordE6 {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k) :
    ¬ ordD 4 (2 ^ (n * k)) ∣ ordE6 (2 ^ n) := by
  intro hdvd
  have hn0 : 0 < n := by omega
  have hnk : 0 < n * k := Nat.mul_pos hn0 (by omega)
  rw [ppdE6_ordD_four_eq hnk] at hdvd
  rcases Nat.lt_or_ge k 3 with hk2 | hk3
  · obtain rfl : k = 2 := by omega
    obtain ⟨r, hr⟩ := exists_isPrimitivePrimeDivisor (k := 8 * n) (by omega) (by omega)
    have hN4 : (2 ^ (n * 2)) ^ 4 - 1 = (2 ^ n) ^ 8 - 1 := by
      rw [← pow_mul, ← pow_mul, show n * 2 * 4 = n * 8 by ring]
    have hNpos : 0 < (2 ^ n) ^ 8 - 1 := by
      have : 1 < (2 ^ n) ^ 8 := Nat.one_lt_pow (by norm_num) (Nat.one_lt_two_pow (by omega))
      omega
    have hrN : r ∣ (2 ^ n) ^ 8 - 1 := (ppdE6_dvd_pow_sub_one_iff hr (by norm_num) hn0 8).mpr dvd_rfl
    have hC : ¬ r ∣ (2 ^ n) ^ 36 * ([12, 9, 6, 5, 2].map fun e => (2 ^ n) ^ e - 1).prod := by
      intro hC
      rcases hr.prime.dvd_mul.mp hC with h | h
      · exact ppdE6_not_dvd_pow hr (by norm_num) hn0 36 h
      · obtain ⟨e, he, hd⟩ := ppdE6_dvd_listProd hr (by norm_num) hn0 [12, 9, 6, 5, 2] h
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
        rcases he with rfl | rfl | rfl | rfl | rfl <;> exact absurd hd (by decide)
    refine ppdE6_mult_contra hNpos hrN hC ?_ hdvd ((ordE6_dvd_prod (2 ^ n)).trans (Eq.dvd ?_))
    · exact ⟨(2 ^ (n * 2)) ^ 12 * ((2 ^ (n * 2)) ^ 2 - 1) * ((2 ^ (n * 2)) ^ 6 - 1),
        by rw [hN4]; ring⟩
    · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
      ring
  · have hk0 : 0 < k := by omega
    obtain ⟨r, hr⟩ := exists_isPrimitivePrimeDivisor (k := 6 * k * n) (by nlinarith)
      (by nlinarith)
    have hr' : IsPrimitivePrimeDivisor r (6 * (n * k)) := by
      rw [show 6 * (n * k) = 6 * k * n by ring]
      exact hr
    have hrA : r ∣ (2 ^ (n * k)) ^ 12 * ((2 ^ (n * k)) ^ 2 - 1) * ((2 ^ (n * k)) ^ 6 - 1) *
        ((2 ^ (n * k)) ^ 4 - 1) ^ 2 := by
      refine Dvd.dvd.mul_right (Dvd.dvd.mul_left ?_ _) _
      exact (ppdE6_dvd_pow_sub_one_iff hr' (by norm_num) hnk 6).mpr dvd_rfl
    have h1 := (hrA.trans hdvd).trans (ordE6_dvd_prod (2 ^ n))
    have h2 := (hr.prime.dvd_mul.mp h1).resolve_left (ppdE6_not_dvd_pow hr (by omega) hn0 36)
    obtain ⟨e, he, hd⟩ := ppdE6_dvd_listProd (m := 6 * k) hr (by omega) hn0 _ h2
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
      (have := Nat.le_of_dvd (by norm_num) hd; omega)

theorem ordD_four_not_dvd_ordTwistedE6 {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k) :
    ¬ ordD 4 (2 ^ (n * k)) ∣ ordTwistedE6 (2 ^ n) := by
  intro hdvd
  have hn0 : 0 < n := by omega
  have hnk : 0 < n * k := Nat.mul_pos hn0 (by omega)
  have hq : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  rw [ppdE6_ordD_four_eq hnk] at hdvd
  have hB := ordTwistedE6_dvd_prod hq
  rcases Nat.lt_or_ge k 4 with hk4 | hk4
  · rcases (by omega : k = 2 ∨ k = 3) with rfl | rfl
    · obtain ⟨r, hr⟩ := exists_isPrimitivePrimeDivisor (k := 8 * n) (by omega) (by omega)
      have hN4 : (2 ^ (n * 2)) ^ 4 - 1 = (2 ^ n) ^ 8 - 1 := by
        rw [← pow_mul, ← pow_mul, show n * 2 * 4 = n * 8 by ring]
      have hNpos : 0 < (2 ^ n) ^ 8 - 1 := by
        have : 1 < (2 ^ n) ^ 8 := Nat.one_lt_pow (by norm_num) (Nat.one_lt_two_pow (by omega))
        omega
      have hrN : r ∣ (2 ^ n) ^ 8 - 1 :=
        (ppdE6_dvd_pow_sub_one_iff hr (by norm_num) hn0 8).mpr dvd_rfl
      have hC : ¬ r ∣ (2 ^ n) ^ 36 * ([12, 18, 6, 10, 2].map fun e => (2 ^ n) ^ e - 1).prod := by
        intro hC
        rcases hr.prime.dvd_mul.mp hC with h | h
        · exact ppdE6_not_dvd_pow hr (by norm_num) hn0 36 h
        · obtain ⟨e, he, hd⟩ := ppdE6_dvd_listProd hr (by norm_num) hn0 [12, 18, 6, 10, 2] h
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
          rcases he with rfl | rfl | rfl | rfl | rfl <;> exact absurd hd (by decide)
      refine ppdE6_mult_contra hNpos hrN hC ?_ hdvd (hB.trans (Eq.dvd ?_))
      · exact ⟨(2 ^ (n * 2)) ^ 12 * ((2 ^ (n * 2)) ^ 2 - 1) * ((2 ^ (n * 2)) ^ 6 - 1),
          by rw [hN4]; ring⟩
      · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
        ring
    · obtain ⟨r, hr⟩ := exists_isPrimitivePrimeDivisor (k := 12 * n) (by omega) (by omega)
      have hN4 : (2 ^ (n * 3)) ^ 4 - 1 = (2 ^ n) ^ 12 - 1 := by
        rw [← pow_mul, ← pow_mul, show n * 3 * 4 = n * 12 by ring]
      have hNpos : 0 < (2 ^ n) ^ 12 - 1 := by
        have : 1 < (2 ^ n) ^ 12 := Nat.one_lt_pow (by norm_num) (Nat.one_lt_two_pow (by omega))
        omega
      have hrN : r ∣ (2 ^ n) ^ 12 - 1 :=
        (ppdE6_dvd_pow_sub_one_iff hr (by norm_num) hn0 12).mpr dvd_rfl
      have hC : ¬ r ∣ (2 ^ n) ^ 36 * ([18, 8, 6, 10, 2].map fun e => (2 ^ n) ^ e - 1).prod := by
        intro hC
        rcases hr.prime.dvd_mul.mp hC with h | h
        · exact ppdE6_not_dvd_pow hr (by norm_num) hn0 36 h
        · obtain ⟨e, he, hd⟩ := ppdE6_dvd_listProd hr (by norm_num) hn0 [18, 8, 6, 10, 2] h
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
          rcases he with rfl | rfl | rfl | rfl | rfl <;> exact absurd hd (by decide)
      refine ppdE6_mult_contra hNpos hrN hC ?_ hdvd (hB.trans (Eq.dvd ?_))
      · exact ⟨(2 ^ (n * 3)) ^ 12 * ((2 ^ (n * 3)) ^ 2 - 1) * ((2 ^ (n * 3)) ^ 6 - 1),
          by rw [hN4]; ring⟩
      · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
        ring
  · have hk0 : 0 < k := by omega
    obtain ⟨r, hr⟩ := exists_isPrimitivePrimeDivisor (k := 6 * k * n) (by nlinarith)
      (by nlinarith)
    have hr' : IsPrimitivePrimeDivisor r (6 * (n * k)) := by
      rw [show 6 * (n * k) = 6 * k * n by ring]
      exact hr
    have hrA : r ∣ (2 ^ (n * k)) ^ 12 * ((2 ^ (n * k)) ^ 2 - 1) * ((2 ^ (n * k)) ^ 6 - 1) *
        ((2 ^ (n * k)) ^ 4 - 1) ^ 2 := by
      refine Dvd.dvd.mul_right (Dvd.dvd.mul_left ?_ _) _
      exact (ppdE6_dvd_pow_sub_one_iff hr' (by norm_num) hnk 6).mpr dvd_rfl
    have h1 := (hrA.trans hdvd).trans hB
    have h2 := (hr.prime.dvd_mul.mp h1).resolve_left (ppdE6_not_dvd_pow hr (by omega) hn0 36)
    obtain ⟨e, he, hd⟩ := ppdE6_dvd_listProd (m := 6 * k) hr (by omega) hn0 _ h2
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
      (have := Nat.le_of_dvd (by norm_num) hd; omega)

theorem ordTrialityD4_not_dvd_ordTwistedE6 {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k) :
    ¬ ordTrialityD4 (2 ^ (n * k)) ∣ ordTwistedE6 (2 ^ n) := by
  intro hdvd
  have hn0 : 0 < n := by omega
  have hk0 : 0 < k := by omega
  have hnk : 0 < n * k := Nat.mul_pos hn0 hk0
  have hq : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  obtain ⟨r, hr⟩ := exists_isPrimitivePrimeDivisor (k := 12 * k * n) (by nlinarith)
    (by nlinarith)
  have hr' : IsPrimitivePrimeDivisor r (12 * (n * k)) := by
    rw [show 12 * (n * k) = 12 * k * n by ring]
    exact hr
  have hrA : r ∣ ordTrialityD4 (2 ^ (n * k)) := by
    have h12 : 12 * (n * k) ∣ (n * k) * 12 := ⟨1, by ring⟩
    have h4 : ¬ 12 * (n * k) ∣ (n * k) * 4 := by
      intro h
      have := Nat.le_of_dvd (by omega) h
      omega
    have hT := PrimDiv.dvd_triality_of hr' (Nat.mul_pos (by norm_num) hnk) (n * k) h12 h4
    unfold ordTrialityD4
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_left hT _) _) _
  have h1 := (hrA.trans hdvd).trans (ordTwistedE6_dvd_prod hq)
  have h2 := (hr.prime.dvd_mul.mp h1).resolve_left (ppdE6_not_dvd_pow hr (by omega) hn0 36)
  obtain ⟨e, he, hd⟩ := ppdE6_dvd_listProd (m := 12 * k) hr (by omega) hn0 _ h2
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (have := Nat.le_of_dvd (by norm_num) hd; omega)

end CFSG.Timmesfeld.Orders

end
