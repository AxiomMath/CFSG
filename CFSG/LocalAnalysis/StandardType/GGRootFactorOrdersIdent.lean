module

public import CFSG.LocalAnalysis.StandardType.GGStructSOnePrimeRootCount

public section

namespace CFSG.StandardType

open CFSG.Open

private lemma odd_two_pow_sub_one {f : ℕ} (hf : 0 < f) : Odd (2 ^ f - 1) :=
  Nat.Even.sub_odd Nat.one_le_two_pow
    (even_iff_two_dvd.mpr (dvd_pow_self 2 hf.ne')) odd_one

private lemma odd_two_pow_add_one {f : ℕ} (hf : 0 < f) : Odd (2 ^ f + 1) :=
  Even.add_odd (even_iff_two_dvd.mpr (dvd_pow_self 2 hf.ne')) odd_one

private lemma gcd_two_odd {n : ℕ} (hn : Odd n) : Nat.gcd 2 n = 1 :=
  (Nat.coprime_two_left.mpr hn).gcd_eq_one

private lemma gcd_four_odd {n : ℕ} (hn : Odd n) : Nat.gcd 4 n = 1 := by
  have h : Nat.Coprime 4 n := by
    simpa using (Nat.coprime_two_left.mpr hn).pow_left 2
  exact h.gcd_eq_one

private lemma le_half_mul_succ {k : ℕ} (hk : 1 ≤ k) : k ≤ k * (k + 1) / 2 := by
  rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
  nlinarith

private lemma le_mul_pred {k : ℕ} (hk : 2 ≤ k) : k ≤ k * (k - 1) := by
  have h : k * 1 ≤ k * (k - 1) := Nat.mul_le_mul_left k (by omega)
  simpa using h

private lemma le_mul_self {k : ℕ} (hk : 1 ≤ k) : k ≤ k * k := by
  have h : k * 1 ≤ k * k := Nat.mul_le_mul_left k hk
  simpa using h

private lemma two_pow_le_of_dvd_60 {b : ℕ} (h : 2 ^ b ∣ 60) : b ≤ 2 := by
  by_contra hb
  have h8 : 8 ∣ 2 ^ b := by
    have := Nat.pow_dvd_pow 2 (show 3 ≤ b by omega)
    simpa using this
  exact absurd (h8.trans h) (by norm_num)

private lemma two_pow_le_of_dvd_360 {b : ℕ} (h : 2 ^ b ∣ 360) : b ≤ 3 := by
  by_contra hb
  have h16 : 16 ∣ 2 ^ b := by
    have := Nat.pow_dvd_pow 2 (show 4 ≤ b by omega)
    simpa using this
  exact absurd (h16.trans h) (by norm_num)

private lemma two_pow_le_of_dvd_25920 {b : ℕ} (h : 2 ^ b ∣ 25920) : b ≤ 6 := by
  by_contra hb
  have h128 : 128 ∣ 2 ^ b := by
    have := Nat.pow_dvd_pow 2 (show 7 ≤ b by omega)
    simpa using this
  exact absurd (h128.trans h) (by norm_num)

private lemma two_pow_le_of_dvd_174182400 {b : ℕ} (h : 2 ^ b ∣ 174182400) : b ≤ 12 := by
  by_contra hb
  have h8192 : 8192 ∣ 2 ^ b := by
    have := Nat.pow_dvd_pow 2 (show 13 ≤ b by omega)
    simpa using this
  exact absurd (h8192.trans h) (by norm_num)

private lemma toNat_two (q : ℕ) : (((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2).toNat) = q ^ 2 - 1 := by
  rcases q with _ | q
  · norm_num
  · have h1 : (1 : ℤ) ≤ ((q + 1 : ℕ) : ℤ) ^ 2 := by
      have hq : (1 : ℤ) ≤ ((q + 1 : ℕ) : ℤ) := by omega
      nlinarith
    have hq2 : (1 : ℕ) ≤ (q + 1) ^ 2 := Nat.one_le_pow 2 (q + 1) (by omega)
    have h2 : ((((q + 1 : ℕ) : ℤ) ^ 2 - (1 : ℤ)).toNat) = (q + 1) ^ 2 - 1 := by
      apply Nat.cast_injective (R := ℤ)
      rw [Int.toNat_sub_of_le h1, Nat.cast_sub hq2]
      push_cast
      ring
    simpa using h2

private lemma add_one_dvd_sq_sub_one (q : ℕ) : q + 1 ∣ q ^ 2 - 1 :=
  ⟨q - 1, by rw [← one_pow 2, Nat.sq_sub_sq, one_pow]⟩

private lemma two_pow_dvd_ordA {k f : ℕ} (hk : 0 < k) (hf : 0 < f) :
    2 ^ (f * (k * (k + 1) / 2)) ∣ ordA k (2 ^ f) := by
  unfold ordA
  have hmem : 2 ∈ Finset.Icc 2 (k + 1) := by
    simp only [Finset.mem_Icc]; omega
  have hfac : (2 ^ f) ^ 2 - 1 ∣ ∏ i ∈ Finset.Icc 2 (k + 1), ((2 ^ f) ^ i - 1) :=
    Finset.dvd_prod_of_mem _ hmem
  have hdvd : Nat.gcd (k + 1) (2 ^ f - 1) ∣
      ∏ i ∈ Finset.Icc 2 (k + 1), ((2 ^ f) ^ i - 1) :=
    (Nat.gcd_dvd_right _ _).trans ((Nat.sub_one_dvd_pow_sub_one (2 ^ f) 2).trans hfac)
  rw [Nat.mul_div_assoc _ hdvd]
  rw [show (2 ^ f) ^ (k * (k + 1) / 2) = 2 ^ (f * (k * (k + 1) / 2)) by rw [← pow_mul]]
  exact dvd_mul_right _ _

private lemma two_pow_dvd_ordTwistedA {k f : ℕ} (hk : 0 < k) (hf : 0 < f) :
    2 ^ (f * (k * (k + 1) / 2)) ∣ ordTwistedA k (2 ^ f) := by
  unfold ordTwistedA
  have hmem : 2 ∈ Finset.Icc 2 (k + 1) := by
    simp only [Finset.mem_Icc]; omega
  have hfac : ((((2 ^ f : ℕ) : ℤ) ^ 2 - (-1 : ℤ) ^ 2).toNat) ∣
      ∏ i ∈ Finset.Icc 2 (k + 1), ((((2 ^ f : ℕ) : ℤ) ^ i - (-1 : ℤ) ^ i).toNat) :=
    Finset.dvd_prod_of_mem _ hmem
  have h1 : 2 ^ f + 1 ∣ ((((2 ^ f : ℕ) : ℤ) ^ 2 - (-1 : ℤ) ^ 2).toNat) := by
    rw [toNat_two]
    exact add_one_dvd_sq_sub_one (2 ^ f)
  have hdvd : Nat.gcd (k + 1) (2 ^ f + 1) ∣
      ∏ i ∈ Finset.Icc 2 (k + 1), ((((2 ^ f : ℕ) : ℤ) ^ i - (-1 : ℤ) ^ i).toNat) :=
    (Nat.gcd_dvd_right _ _).trans (h1.trans hfac)
  rw [Nat.mul_div_assoc _ hdvd]
  rw [show (2 ^ f) ^ (k * (k + 1) / 2) = 2 ^ (f * (k * (k + 1) / 2)) by rw [← pow_mul]]
  exact dvd_mul_right _ _

private lemma two_pow_dvd_ordBC {k f : ℕ} (hf : 0 < f) :
    2 ^ (f * (k * k)) ∣ ordBC k (2 ^ f) := by
  unfold ordBC
  rw [gcd_two_odd (odd_two_pow_sub_one hf), Nat.div_one,
    show (2 ^ f) ^ (k * k) = 2 ^ (f * (k * k)) by rw [← pow_mul]]
  exact dvd_mul_right _ _

private lemma ordD_eq {k f : ℕ} (hk : 1 ≤ k) (hf : 0 < f) :
    ordD k (2 ^ f) = 2 ^ (f * (k * (k - 1))) *
      (((2 ^ f) ^ k - 1) * ∏ i ∈ Finset.Icc 1 (k - 1), ((2 ^ f) ^ (2 * i) - 1)) := by
  unfold ordD
  have hodd : Odd ((2 ^ f) ^ k - 1) := by
    rw [← pow_mul]
    exact odd_two_pow_sub_one (by positivity)
  rw [gcd_four_odd hodd, Nat.div_one,
    show (2 ^ f) ^ (k * (k - 1)) = 2 ^ (f * (k * (k - 1))) by rw [← pow_mul]]
  ring

private lemma ordTwistedD_eq {k f : ℕ} (hk : 1 ≤ k) (hf : 0 < f) :
    ordTwistedD k (2 ^ f) = 2 ^ (f * (k * (k - 1))) *
      (((2 ^ f) ^ k + 1) * ∏ i ∈ Finset.Icc 1 (k - 1), ((2 ^ f) ^ (2 * i) - 1)) := by
  unfold ordTwistedD
  have hodd : Odd ((2 ^ f) ^ k + 1) := by
    rw [← pow_mul]
    exact odd_two_pow_add_one (by positivity)
  rw [gcd_four_odd hodd, Nat.div_one,
    show (2 ^ f) ^ (k * (k - 1)) = 2 ^ (f * (k * (k - 1))) by rw [← pow_mul]]
  ring

private lemma two_pow_dvd_ordD {k f : ℕ} (hk : 1 ≤ k) (hf : 0 < f) :
    2 ^ (f * (k * (k - 1))) ∣ ordD k (2 ^ f) := by
  rw [ordD_eq hk hf]
  exact dvd_mul_right _ _

private lemma two_pow_dvd_ordTwistedD {k f : ℕ} (hk : 1 ≤ k) (hf : 0 < f) :
    2 ^ (f * (k * (k - 1))) ∣ ordTwistedD k (2 ^ f) := by
  rw [ordTwistedD_eq hk hf]
  exact dvd_mul_right _ _

private lemma ordE7_eq (f : ℕ) (hf : 0 < f) :
    ordE7 (2 ^ f) = 2 ^ (f * 63) * ((2 ^ f) ^ 18 - 1) * ((2 ^ f) ^ 14 - 1) *
      ((2 ^ f) ^ 12 - 1) * ((2 ^ f) ^ 10 - 1) * ((2 ^ f) ^ 8 - 1) *
      ((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 2 - 1) := by
  unfold ordE7
  rw [gcd_two_odd (odd_two_pow_sub_one hf), Nat.div_one,
    show (2 ^ f) ^ 63 = 2 ^ (f * 63) by rw [← pow_mul]]

private lemma two_pow_dvd_ordE7 {f : ℕ} (hf : 0 < f) :
    2 ^ (f * 63) ∣ ordE7 (2 ^ f) := by
  rw [ordE7_eq f hf]
  refine ⟨((2 ^ f) ^ 18 - 1) * ((2 ^ f) ^ 14 - 1) * ((2 ^ f) ^ 12 - 1) *
    ((2 ^ f) ^ 10 - 1) * ((2 ^ f) ^ 8 - 1) * ((2 ^ f) ^ 6 - 1) *
    ((2 ^ f) ^ 2 - 1), ?_⟩
  ring

private lemma odd_ne_even {m N : ℕ} (hm : Odd m) (hN : Even N) (h : m = N) : False := by
  have h1 := Nat.odd_iff.mp hm
  have h2 := Nat.even_iff.mp hN
  omega

private lemma ordA_one_le_one (k : ℕ) : ordA k 1 ≤ 1 := by
  rcases k with _ | k
  · unfold ordA; norm_num
  · rw [show ordA (k + 1) 1 = 0 by simp [ordA]]; omega

private lemma ordTwistedA_one_le_one (k : ℕ) : ordTwistedA k 1 ≤ 1 := by
  rcases k with _ | k
  · unfold ordTwistedA; norm_num
  · have hmem : 2 ∈ Finset.Icc 2 (k + 1 + 1) := by
      simp only [Finset.mem_Icc]; omega
    have hzero : ((((1 : ℕ) : ℤ) ^ 2 - (-1 : ℤ) ^ 2).toNat) = 0 := by norm_num
    have hP : ∏ i ∈ Finset.Icc 2 (k + 1 + 1),
        ((((1 : ℕ) : ℤ) ^ i - (-1 : ℤ) ^ i).toNat) = 0 :=
      Finset.prod_eq_zero hmem hzero
    rw [ordTwistedA, hP, Nat.mul_zero, Nat.zero_div]
    omega

private lemma ordBC_one_le_one (k : ℕ) : ordBC k 1 ≤ 1 := by
  rcases k with _ | k
  · unfold ordBC; norm_num
  · rw [show ordBC (k + 1) 1 = 0 by simp [ordBC]]; omega

private lemma ordD_one_le_one (k : ℕ) : ordD k 1 ≤ 1 := by
  rw [show ordD k 1 = 0 by simp [ordD]]; omega

private lemma ordTwistedD_one_le_one (k : ℕ) : ordTwistedD k 1 ≤ 1 := by
  rcases k with _ | _ | k
  · unfold ordTwistedD; norm_num
  · unfold ordTwistedD; norm_num
  · rw [show ordTwistedD (k + 2) 1 = 0 by simp [ordTwistedD]]; omega

private lemma ordA_one_ne (k N : ℕ) (hN : 2 ≤ N) (h : ordA k 1 = N) : False := by
  have := ordA_one_le_one k
  omega

private lemma ordTwistedA_one_ne (k N : ℕ) (hN : 2 ≤ N) (h : ordTwistedA k 1 = N) : False := by
  have := ordTwistedA_one_le_one k
  omega

private lemma ordBC_one_ne (k N : ℕ) (hN : 2 ≤ N) (h : ordBC k 1 = N) : False := by
  have := ordBC_one_le_one k
  omega

private lemma ordD_one_ne (k N : ℕ) (hN : 2 ≤ N) (h : ordD k 1 = N) : False := by
  have := ordD_one_le_one k
  omega

private lemma ordTwistedD_one_ne (k N : ℕ) (hN : 2 ≤ N)
    (h : ordTwistedD k 1 = N) : False := by
  have := ordTwistedD_one_le_one k
  omega

private lemma ordA_eq_60 {k f : ℕ} (h : ordA k (2 ^ f) = 60) : k = 1 ∧ f = 2 := by
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · exact (ordA_one_ne k 60 (by norm_num) (by simpa using h)).elim
    · exact hf
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · unfold ordA at h; norm_num at h
  · have hdiv : 2 ^ (f * (k * (k + 1) / 2)) ∣ 60 := by
      rw [← h]; exact two_pow_dvd_ordA hk hf
    have hb : f * (k * (k + 1) / 2) ≤ 2 := two_pow_le_of_dvd_60 hdiv
    have hk_le : k ≤ 2 := by
      have h1 : k ≤ k * (k + 1) / 2 := le_half_mul_succ (by omega)
      have h2 : k * (k + 1) / 2 ≤ 2 := by
        have h3 : 1 * (k * (k + 1) / 2) ≤ f * (k * (k + 1) / 2) :=
          Nat.mul_le_mul_right _ (by omega : 1 ≤ f)
        omega
      omega
    have hf_le : f ≤ 2 := by
      have he : 1 ≤ k * (k + 1) / 2 :=
        le_trans (by omega : 1 ≤ k) (le_half_mul_succ (by omega))
      have h3 : f * 1 ≤ f * (k * (k + 1) / 2) := Nat.mul_le_mul_left f he
      omega
    revert h
    interval_cases k <;> interval_cases f <;> first | omega | decide

private lemma ordA_ne_360 {k f : ℕ} (h : ordA k (2 ^ f) = 360) : False := by
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · exact (ordA_one_ne k 360 (by norm_num) (by simpa using h)).elim
    · exact hf
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · unfold ordA at h; norm_num at h
  · have hdiv : 2 ^ (f * (k * (k + 1) / 2)) ∣ 360 := by
      rw [← h]; exact two_pow_dvd_ordA hk hf
    have hb : f * (k * (k + 1) / 2) ≤ 3 := two_pow_le_of_dvd_360 hdiv
    have hk_le : k ≤ 3 := by
      have h1 : k ≤ k * (k + 1) / 2 := le_half_mul_succ (by omega)
      have h2 : k * (k + 1) / 2 ≤ 3 := by
        have h3 : 1 * (k * (k + 1) / 2) ≤ f * (k * (k + 1) / 2) :=
          Nat.mul_le_mul_right _ (by omega : 1 ≤ f)
        omega
      omega
    have hf_le : f ≤ 3 := by
      have he : 1 ≤ k * (k + 1) / 2 :=
        le_trans (by omega : 1 ≤ k) (le_half_mul_succ (by omega))
      have h3 : f * 1 ≤ f * (k * (k + 1) / 2) := Nat.mul_le_mul_left f he
      omega
    revert h
    interval_cases k <;> interval_cases f <;> first | omega | decide

private lemma ordA_ne_25920 {k f : ℕ} (h : ordA k (2 ^ f) = 25920) : False := by
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · exact (ordA_one_ne k 25920 (by norm_num) (by simpa using h)).elim
    · exact hf
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · unfold ordA at h; norm_num at h
  · have hdiv : 2 ^ (f * (k * (k + 1) / 2)) ∣ 25920 := by
      rw [← h]; exact two_pow_dvd_ordA hk hf
    have hb : f * (k * (k + 1) / 2) ≤ 6 := two_pow_le_of_dvd_25920 hdiv
    have hk_le : k ≤ 6 := by
      have h1 : k ≤ k * (k + 1) / 2 := le_half_mul_succ (by omega)
      have h2 : k * (k + 1) / 2 ≤ 6 := by
        have h3 : 1 * (k * (k + 1) / 2) ≤ f * (k * (k + 1) / 2) :=
          Nat.mul_le_mul_right _ (by omega : 1 ≤ f)
        omega
      omega
    have hf_le : f ≤ 6 := by
      have he : 1 ≤ k * (k + 1) / 2 :=
        le_trans (by omega : 1 ≤ k) (le_half_mul_succ (by omega))
      have h3 : f * 1 ≤ f * (k * (k + 1) / 2) := Nat.mul_le_mul_left f he
      omega
    revert h
    interval_cases k <;> interval_cases f <;> first | omega | decide

private lemma ordA_ne_174182400 {k f : ℕ} (h : ordA k (2 ^ f) = 174182400) : False := by
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · exact (ordA_one_ne k 174182400 (by norm_num) (by simpa using h)).elim
    · exact hf
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · unfold ordA at h; norm_num at h
  · have hdiv : 2 ^ (f * (k * (k + 1) / 2)) ∣ 174182400 := by
      rw [← h]; exact two_pow_dvd_ordA hk hf
    have hb : f * (k * (k + 1) / 2) ≤ 12 := two_pow_le_of_dvd_174182400 hdiv
    have hk_le : k ≤ 12 := by
      have h1 : k ≤ k * (k + 1) / 2 := le_half_mul_succ (by omega)
      have h2 : k * (k + 1) / 2 ≤ 12 := by
        have h3 : 1 * (k * (k + 1) / 2) ≤ f * (k * (k + 1) / 2) :=
          Nat.mul_le_mul_right _ (by omega : 1 ≤ f)
        omega
      omega
    have hf_le : f ≤ 12 := by
      have he : 1 ≤ k * (k + 1) / 2 :=
        le_trans (by omega : 1 ≤ k) (le_half_mul_succ (by omega))
      have h3 : f * 1 ≤ f * (k * (k + 1) / 2) := Nat.mul_le_mul_left f he
      omega
    revert h
    interval_cases k <;> interval_cases f <;> first | omega | decide

private lemma ordTwistedA_eq_25920 {k f : ℕ} (h : ordTwistedA k (2 ^ f) = 25920) :
    k = 3 ∧ f = 1 := by
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · exact (ordTwistedA_one_ne k 25920 (by norm_num) (by simpa using h)).elim
    · exact hf
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · unfold ordTwistedA at h; norm_num at h
  · have hdiv : 2 ^ (f * (k * (k + 1) / 2)) ∣ 25920 := by
      rw [← h]; exact two_pow_dvd_ordTwistedA hk hf
    have hb : f * (k * (k + 1) / 2) ≤ 6 := two_pow_le_of_dvd_25920 hdiv
    have hk_le : k ≤ 6 := by
      have h1 : k ≤ k * (k + 1) / 2 := le_half_mul_succ (by omega)
      have h2 : k * (k + 1) / 2 ≤ 6 := by
        have h3 : 1 * (k * (k + 1) / 2) ≤ f * (k * (k + 1) / 2) :=
          Nat.mul_le_mul_right _ (by omega : 1 ≤ f)
        omega
      omega
    have hf_le : f ≤ 6 := by
      have he : 1 ≤ k * (k + 1) / 2 :=
        le_trans (by omega : 1 ≤ k) (le_half_mul_succ (by omega))
      have h3 : f * 1 ≤ f * (k * (k + 1) / 2) := Nat.mul_le_mul_left f he
      omega
    revert h
    interval_cases k <;> interval_cases f <;> first | omega | decide

private lemma ordTwistedA_ne_360 {k f : ℕ} (h : ordTwistedA k (2 ^ f) = 360) : False := by
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · exact (ordTwistedA_one_ne k 360 (by norm_num) (by simpa using h)).elim
    · exact hf
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · unfold ordTwistedA at h; norm_num at h
  · have hdiv : 2 ^ (f * (k * (k + 1) / 2)) ∣ 360 := by
      rw [← h]; exact two_pow_dvd_ordTwistedA hk hf
    have hb : f * (k * (k + 1) / 2) ≤ 3 := two_pow_le_of_dvd_360 hdiv
    have hk_le : k ≤ 3 := by
      have h1 : k ≤ k * (k + 1) / 2 := le_half_mul_succ (by omega)
      have h2 : k * (k + 1) / 2 ≤ 3 := by
        have h3 : 1 * (k * (k + 1) / 2) ≤ f * (k * (k + 1) / 2) :=
          Nat.mul_le_mul_right _ (by omega : 1 ≤ f)
        omega
      omega
    have hf_le : f ≤ 3 := by
      have he : 1 ≤ k * (k + 1) / 2 :=
        le_trans (by omega : 1 ≤ k) (le_half_mul_succ (by omega))
      have h3 : f * 1 ≤ f * (k * (k + 1) / 2) := Nat.mul_le_mul_left f he
      omega
    revert h
    interval_cases k <;> interval_cases f <;> first | omega | decide

private lemma ordTwistedA_ne_174182400 {k f : ℕ}
    (h : ordTwistedA k (2 ^ f) = 174182400) : False := by
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · exact (ordTwistedA_one_ne k 174182400 (by norm_num) (by simpa using h)).elim
    · exact hf
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · unfold ordTwistedA at h; norm_num at h
  · have hdiv : 2 ^ (f * (k * (k + 1) / 2)) ∣ 174182400 := by
      rw [← h]; exact two_pow_dvd_ordTwistedA hk hf
    have hb : f * (k * (k + 1) / 2) ≤ 12 := two_pow_le_of_dvd_174182400 hdiv
    have hk_le : k ≤ 12 := by
      have h1 : k ≤ k * (k + 1) / 2 := le_half_mul_succ (by omega)
      have h2 : k * (k + 1) / 2 ≤ 12 := by
        have h3 : 1 * (k * (k + 1) / 2) ≤ f * (k * (k + 1) / 2) :=
          Nat.mul_le_mul_right _ (by omega : 1 ≤ f)
        omega
      omega
    have hf_le : f ≤ 12 := by
      have he : 1 ≤ k * (k + 1) / 2 :=
        le_trans (by omega : 1 ≤ k) (le_half_mul_succ (by omega))
      have h3 : f * 1 ≤ f * (k * (k + 1) / 2) := Nat.mul_le_mul_left f he
      omega
    revert h
    interval_cases k <;> interval_cases f <;> first | omega | decide

private lemma ordBC_zero {f : ℕ} (hf : 0 < f) : ordBC 0 (2 ^ f) = 1 := by
  unfold ordBC
  rw [gcd_two_odd (odd_two_pow_sub_one hf), Nat.div_one]
  norm_num

private lemma ordBC_eq_60 {k f : ℕ} (h : ordBC k (2 ^ f) = 60) : k = 1 ∧ f = 2 := by
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · exact (ordBC_one_ne k 60 (by norm_num) (by simpa using h)).elim
    · exact hf
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [ordBC_zero hf] at h; omega
  · have hdiv : 2 ^ (f * (k * k)) ∣ 60 := by
      rw [← h]; exact two_pow_dvd_ordBC hf
    have hb : f * (k * k) ≤ 2 := two_pow_le_of_dvd_60 hdiv
    have hk_le : k ≤ 2 := by
      have h1 : k ≤ k * k := le_mul_self (by omega)
      have h2 : k * k ≤ 2 := by
        have h3 : 1 * (k * k) ≤ f * (k * k) :=
          Nat.mul_le_mul_right _ (by omega : 1 ≤ f)
        omega
      omega
    have hf_le : f ≤ 2 := by
      have he : 1 ≤ k * k := by nlinarith
      have h3 : f * 1 ≤ f * (k * k) := Nat.mul_le_mul_left f he
      omega
    revert h
    interval_cases k <;> interval_cases f <;> first | omega | decide

private lemma ordBC_ne_360 {k f : ℕ} (h : ordBC k (2 ^ f) = 360) : False := by
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · exact (ordBC_one_ne k 360 (by norm_num) (by simpa using h)).elim
    · exact hf
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [ordBC_zero hf] at h; omega
  · have hdiv : 2 ^ (f * (k * k)) ∣ 360 := by
      rw [← h]; exact two_pow_dvd_ordBC hf
    have hb : f * (k * k) ≤ 3 := two_pow_le_of_dvd_360 hdiv
    have hk_le : k ≤ 3 := by
      have h1 : k ≤ k * k := le_mul_self (by omega)
      have h2 : k * k ≤ 3 := by
        have h3 : 1 * (k * k) ≤ f * (k * k) :=
          Nat.mul_le_mul_right _ (by omega : 1 ≤ f)
        omega
      omega
    have hf_le : f ≤ 3 := by
      have he : 1 ≤ k * k := by nlinarith
      have h3 : f * 1 ≤ f * (k * k) := Nat.mul_le_mul_left f he
      omega
    revert h
    interval_cases k <;> interval_cases f <;> first | omega | decide

private lemma ordBC_ne_25920 {k f : ℕ} (h : ordBC k (2 ^ f) = 25920) : False := by
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · exact (ordBC_one_ne k 25920 (by norm_num) (by simpa using h)).elim
    · exact hf
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [ordBC_zero hf] at h; omega
  · have hdiv : 2 ^ (f * (k * k)) ∣ 25920 := by
      rw [← h]; exact two_pow_dvd_ordBC hf
    have hb : f * (k * k) ≤ 6 := two_pow_le_of_dvd_25920 hdiv
    have hk_le : k ≤ 6 := by
      have h1 : k ≤ k * k := le_mul_self (by omega)
      have h2 : k * k ≤ 6 := by
        have h3 : 1 * (k * k) ≤ f * (k * k) :=
          Nat.mul_le_mul_right _ (by omega : 1 ≤ f)
        omega
      omega
    have hf_le : f ≤ 6 := by
      have he : 1 ≤ k * k := by nlinarith
      have h3 : f * 1 ≤ f * (k * k) := Nat.mul_le_mul_left f he
      omega
    revert h
    interval_cases k <;> interval_cases f <;> first | omega | decide

private lemma ordBC_ne_174182400 {k f : ℕ} (h : ordBC k (2 ^ f) = 174182400) : False := by
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · exact (ordBC_one_ne k 174182400 (by norm_num) (by simpa using h)).elim
    · exact hf
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [ordBC_zero hf] at h; omega
  · have hdiv : 2 ^ (f * (k * k)) ∣ 174182400 := by
      rw [← h]; exact two_pow_dvd_ordBC hf
    have hb : f * (k * k) ≤ 12 := two_pow_le_of_dvd_174182400 hdiv
    have hk_le : k ≤ 12 := by
      have h1 : k ≤ k * k := le_mul_self (by omega)
      have h2 : k * k ≤ 12 := by
        have h3 : 1 * (k * k) ≤ f * (k * k) :=
          Nat.mul_le_mul_right _ (by omega : 1 ≤ f)
        omega
      omega
    have hf_le : f ≤ 12 := by
      have he : 1 ≤ k * k := by nlinarith
      have h3 : f * 1 ≤ f * (k * k) := Nat.mul_le_mul_left f he
      omega
    revert h
    interval_cases k <;> interval_cases f <;> first | omega | decide

private lemma ordD_ne_60 {k f : ℕ} (h : ordD k (2 ^ f) = 60) : False := by
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · exact (ordD_one_ne k 60 (by norm_num) (by simpa using h)).elim
    · exact hf
  rcases k with _ | _ | k
  · unfold ordD at h; norm_num at h
  · have h1 : ordD 1 (2 ^ f) = 2 ^ f - 1 := by
      rw [ordD_eq (by omega) hf]; simp
    rw [h1] at h
    exact odd_ne_even (odd_two_pow_sub_one hf) (by norm_num : Even 60) h
  · have hdiv : 2 ^ (f * ((k + 2) * ((k + 2) - 1))) ∣ 60 := by
      rw [← h]; exact two_pow_dvd_ordD (by omega) hf
    have hb : f * ((k + 2) * ((k + 2) - 1)) ≤ 2 := two_pow_le_of_dvd_60 hdiv
    have hk_le : k ≤ 2 := by
      have h1 : k + 2 ≤ (k + 2) * ((k + 2) - 1) := le_mul_pred (by omega)
      have h2 : (k + 2) * ((k + 2) - 1) ≤ 2 := by
        have h3 : 1 * ((k + 2) * ((k + 2) - 1)) ≤
            f * ((k + 2) * ((k + 2) - 1)) :=
          Nat.mul_le_mul_right _ (by omega : 1 ≤ f)
        omega
      omega
    have hf_le : f ≤ 2 := by
      have he : 1 ≤ (k + 2) * ((k + 2) - 1) := by
        have := le_mul_pred (k := k + 2) (by omega)
        omega
      have h3 : f * 1 ≤ f * ((k + 2) * ((k + 2) - 1)) := Nat.mul_le_mul_left f he
      omega
    revert h
    interval_cases k <;> interval_cases f <;> first | omega | decide

private lemma ordD_ne_360 {k f : ℕ} (h : ordD k (2 ^ f) = 360) : False := by
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · exact (ordD_one_ne k 360 (by norm_num) (by simpa using h)).elim
    · exact hf
  rcases k with _ | _ | k
  · unfold ordD at h; norm_num at h
  · have h1 : ordD 1 (2 ^ f) = 2 ^ f - 1 := by
      rw [ordD_eq (by omega) hf]; simp
    rw [h1] at h
    exact odd_ne_even (odd_two_pow_sub_one hf) (by norm_num : Even 360) h
  · have hdiv : 2 ^ (f * ((k + 2) * ((k + 2) - 1))) ∣ 360 := by
      rw [← h]; exact two_pow_dvd_ordD (by omega) hf
    have hb : f * ((k + 2) * ((k + 2) - 1)) ≤ 3 := two_pow_le_of_dvd_360 hdiv
    have hk_le : k ≤ 3 := by
      have h1 : k + 2 ≤ (k + 2) * ((k + 2) - 1) := le_mul_pred (by omega)
      have h2 : (k + 2) * ((k + 2) - 1) ≤ 3 := by
        have h3 : 1 * ((k + 2) * ((k + 2) - 1)) ≤
            f * ((k + 2) * ((k + 2) - 1)) :=
          Nat.mul_le_mul_right _ (by omega : 1 ≤ f)
        omega
      omega
    have hf_le : f ≤ 3 := by
      have he : 1 ≤ (k + 2) * ((k + 2) - 1) := by
        have := le_mul_pred (k := k + 2) (by omega)
        omega
      have h3 : f * 1 ≤ f * ((k + 2) * ((k + 2) - 1)) := Nat.mul_le_mul_left f he
      omega
    revert h
    interval_cases k <;> interval_cases f <;> first | omega | decide

private lemma ordD_ne_25920 {k f : ℕ} (h : ordD k (2 ^ f) = 25920) : False := by
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · exact (ordD_one_ne k 25920 (by norm_num) (by simpa using h)).elim
    · exact hf
  rcases k with _ | _ | k
  · unfold ordD at h; norm_num at h
  · have h1 : ordD 1 (2 ^ f) = 2 ^ f - 1 := by
      rw [ordD_eq (by omega) hf]; simp
    rw [h1] at h
    exact odd_ne_even (odd_two_pow_sub_one hf) (by norm_num : Even 25920) h
  · have hdiv : 2 ^ (f * ((k + 2) * ((k + 2) - 1))) ∣ 25920 := by
      rw [← h]; exact two_pow_dvd_ordD (by omega) hf
    have hb : f * ((k + 2) * ((k + 2) - 1)) ≤ 6 := two_pow_le_of_dvd_25920 hdiv
    have hk_le : k ≤ 6 := by
      have h1 : k + 2 ≤ (k + 2) * ((k + 2) - 1) := le_mul_pred (by omega)
      have h2 : (k + 2) * ((k + 2) - 1) ≤ 6 := by
        have h3 : 1 * ((k + 2) * ((k + 2) - 1)) ≤
            f * ((k + 2) * ((k + 2) - 1)) :=
          Nat.mul_le_mul_right _ (by omega : 1 ≤ f)
        omega
      omega
    have hf_le : f ≤ 6 := by
      have he : 1 ≤ (k + 2) * ((k + 2) - 1) := by
        have := le_mul_pred (k := k + 2) (by omega)
        omega
      have h3 : f * 1 ≤ f * ((k + 2) * ((k + 2) - 1)) := Nat.mul_le_mul_left f he
      omega
    revert h
    interval_cases k <;> interval_cases f <;> first | omega | decide

private lemma ordD_eq_174182400 {k f : ℕ} (h : ordD k (2 ^ f) = 174182400) :
    k = 4 ∧ f = 1 := by
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · exact (ordD_one_ne k 174182400 (by norm_num) (by simpa using h)).elim
    · exact hf
  rcases k with _ | _ | k
  · unfold ordD at h; norm_num at h
  · have h1 : ordD 1 (2 ^ f) = 2 ^ f - 1 := by
      rw [ordD_eq (by omega) hf]; simp
    rw [h1] at h
    exact (odd_ne_even (odd_two_pow_sub_one hf) (by norm_num : Even 174182400) h).elim
  · have hdiv : 2 ^ (f * ((k + 2) * ((k + 2) - 1))) ∣ 174182400 := by
      rw [← h]; exact two_pow_dvd_ordD (by omega) hf
    have hb : f * ((k + 2) * ((k + 2) - 1)) ≤ 12 := two_pow_le_of_dvd_174182400 hdiv
    have hk_le : k ≤ 12 := by
      have h1 : k + 2 ≤ (k + 2) * ((k + 2) - 1) := le_mul_pred (by omega)
      have h2 : (k + 2) * ((k + 2) - 1) ≤ 12 := by
        have h3 : 1 * ((k + 2) * ((k + 2) - 1)) ≤
            f * ((k + 2) * ((k + 2) - 1)) :=
          Nat.mul_le_mul_right _ (by omega : 1 ≤ f)
        omega
      omega
    have hf_le : f ≤ 12 := by
      have he : 1 ≤ (k + 2) * ((k + 2) - 1) := by
        have := le_mul_pred (k := k + 2) (by omega)
        omega
      have h3 : f * 1 ≤ f * ((k + 2) * ((k + 2) - 1)) := Nat.mul_le_mul_left f he
      omega
    revert h
    interval_cases k <;> interval_cases f <;> first | omega | decide

private lemma ordTwistedD_zero (f : ℕ) : ordTwistedD 0 (2 ^ f) = 1 := by
  unfold ordTwistedD
  norm_num

private lemma ordTwistedD_eq_60 {k f : ℕ} (h : ordTwistedD k (2 ^ f) = 60) :
    k = 2 ∧ f = 1 := by
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · exact (ordTwistedD_one_ne k 60 (by norm_num) (by simpa using h)).elim
    · exact hf
  rcases k with _ | _ | k
  · rw [ordTwistedD_zero f] at h; omega
  · have h1 : ordTwistedD 1 (2 ^ f) = 2 ^ f + 1 := by
      rw [ordTwistedD_eq (by omega) hf]; simp
    rw [h1] at h
    exact (odd_ne_even (odd_two_pow_add_one hf) (by norm_num : Even 60) h).elim
  · have hdiv : 2 ^ (f * ((k + 2) * ((k + 2) - 1))) ∣ 60 := by
      rw [← h]; exact two_pow_dvd_ordTwistedD (by omega) hf
    have hb : f * ((k + 2) * ((k + 2) - 1)) ≤ 2 := two_pow_le_of_dvd_60 hdiv
    have hk_le : k ≤ 2 := by
      have h1 : k + 2 ≤ (k + 2) * ((k + 2) - 1) := le_mul_pred (by omega)
      have h2 : (k + 2) * ((k + 2) - 1) ≤ 2 := by
        have h3 : 1 * ((k + 2) * ((k + 2) - 1)) ≤
            f * ((k + 2) * ((k + 2) - 1)) :=
          Nat.mul_le_mul_right _ (by omega : 1 ≤ f)
        omega
      omega
    have hf_le : f ≤ 2 := by
      have he : 1 ≤ (k + 2) * ((k + 2) - 1) := by
        have := le_mul_pred (k := k + 2) (by omega)
        omega
      have h3 : f * 1 ≤ f * ((k + 2) * ((k + 2) - 1)) := Nat.mul_le_mul_left f he
      omega
    revert h
    interval_cases k <;> interval_cases f <;> first | omega | decide

private lemma ordTwistedD_ne_360 {k f : ℕ} (h : ordTwistedD k (2 ^ f) = 360) : False := by
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · exact (ordTwistedD_one_ne k 360 (by norm_num) (by simpa using h)).elim
    · exact hf
  rcases k with _ | _ | k
  · rw [ordTwistedD_zero f] at h; omega
  · have h1 : ordTwistedD 1 (2 ^ f) = 2 ^ f + 1 := by
      rw [ordTwistedD_eq (by omega) hf]; simp
    rw [h1] at h
    exact odd_ne_even (odd_two_pow_add_one hf) (by norm_num : Even 360) h
  · have hdiv : 2 ^ (f * ((k + 2) * ((k + 2) - 1))) ∣ 360 := by
      rw [← h]; exact two_pow_dvd_ordTwistedD (by omega) hf
    have hb : f * ((k + 2) * ((k + 2) - 1)) ≤ 3 := two_pow_le_of_dvd_360 hdiv
    have hk_le : k ≤ 3 := by
      have h1 : k + 2 ≤ (k + 2) * ((k + 2) - 1) := le_mul_pred (by omega)
      have h2 : (k + 2) * ((k + 2) - 1) ≤ 3 := by
        have h3 : 1 * ((k + 2) * ((k + 2) - 1)) ≤
            f * ((k + 2) * ((k + 2) - 1)) :=
          Nat.mul_le_mul_right _ (by omega : 1 ≤ f)
        omega
      omega
    have hf_le : f ≤ 3 := by
      have he : 1 ≤ (k + 2) * ((k + 2) - 1) := by
        have := le_mul_pred (k := k + 2) (by omega)
        omega
      have h3 : f * 1 ≤ f * ((k + 2) * ((k + 2) - 1)) := Nat.mul_le_mul_left f he
      omega
    revert h
    interval_cases k <;> interval_cases f <;> first | omega | decide

private lemma ordTwistedD_eq_25920 {k f : ℕ} (h : ordTwistedD k (2 ^ f) = 25920) :
    k = 3 ∧ f = 1 := by
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · exact (ordTwistedD_one_ne k 25920 (by norm_num) (by simpa using h)).elim
    · exact hf
  rcases k with _ | _ | k
  · rw [ordTwistedD_zero f] at h; omega
  · have h1 : ordTwistedD 1 (2 ^ f) = 2 ^ f + 1 := by
      rw [ordTwistedD_eq (by omega) hf]; simp
    rw [h1] at h
    exact (odd_ne_even (odd_two_pow_add_one hf) (by norm_num : Even 25920) h).elim
  · have hdiv : 2 ^ (f * ((k + 2) * ((k + 2) - 1))) ∣ 25920 := by
      rw [← h]; exact two_pow_dvd_ordTwistedD (by omega) hf
    have hb : f * ((k + 2) * ((k + 2) - 1)) ≤ 6 := two_pow_le_of_dvd_25920 hdiv
    have hk_le : k ≤ 6 := by
      have h1 : k + 2 ≤ (k + 2) * ((k + 2) - 1) := le_mul_pred (by omega)
      have h2 : (k + 2) * ((k + 2) - 1) ≤ 6 := by
        have h3 : 1 * ((k + 2) * ((k + 2) - 1)) ≤
            f * ((k + 2) * ((k + 2) - 1)) :=
          Nat.mul_le_mul_right _ (by omega : 1 ≤ f)
        omega
      omega
    have hf_le : f ≤ 6 := by
      have he : 1 ≤ (k + 2) * ((k + 2) - 1) := by
        have := le_mul_pred (k := k + 2) (by omega)
        omega
      have h3 : f * 1 ≤ f * ((k + 2) * ((k + 2) - 1)) := Nat.mul_le_mul_left f he
      omega
    revert h
    interval_cases k <;> interval_cases f <;> first | omega | decide

private lemma ordTwistedD_ne_174182400 {k f : ℕ}
    (h : ordTwistedD k (2 ^ f) = 174182400) : False := by
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · exact (ordTwistedD_one_ne k 174182400 (by norm_num) (by simpa using h)).elim
    · exact hf
  rcases k with _ | _ | k
  · rw [ordTwistedD_zero f] at h; omega
  · have h1 : ordTwistedD 1 (2 ^ f) = 2 ^ f + 1 := by
      rw [ordTwistedD_eq (by omega) hf]; simp
    rw [h1] at h
    exact (odd_ne_even (odd_two_pow_add_one hf) (by norm_num : Even 174182400) h).elim
  · have hdiv : 2 ^ (f * ((k + 2) * ((k + 2) - 1))) ∣ 174182400 := by
      rw [← h]; exact two_pow_dvd_ordTwistedD (by omega) hf
    have hb : f * ((k + 2) * ((k + 2) - 1)) ≤ 12 := two_pow_le_of_dvd_174182400 hdiv
    have hk_le : k ≤ 12 := by
      have h1 : k + 2 ≤ (k + 2) * ((k + 2) - 1) := le_mul_pred (by omega)
      have h2 : (k + 2) * ((k + 2) - 1) ≤ 12 := by
        have h3 : 1 * ((k + 2) * ((k + 2) - 1)) ≤
            f * ((k + 2) * ((k + 2) - 1)) :=
          Nat.mul_le_mul_right _ (by omega : 1 ≤ f)
        omega
      omega
    have hf_le : f ≤ 12 := by
      have he : 1 ≤ (k + 2) * ((k + 2) - 1) := by
        have := le_mul_pred (k := k + 2) (by omega)
        omega
      have h3 : f * 1 ≤ f * ((k + 2) * ((k + 2) - 1)) := Nat.mul_le_mul_left f he
      omega
    revert h
    interval_cases k <;> interval_cases f <;> first | omega | decide

private lemma ordE7_ne {f N : ℕ} (hN2 : 2 ≤ N) (hN : N ≤ 174182400)
    (h : ordE7 (2 ^ f) = N) : False := by
  rcases Nat.eq_zero_or_pos f with rfl | hf
  · have h0 : ordE7 (2 ^ 0) = 0 := by norm_num [ordE7]
    rw [h0] at h
    omega
  · have hdiv : 2 ^ (f * 63) ∣ N := by
      rw [← h]; exact two_pow_dvd_ordE7 hf
    have hle : 2 ^ (f * 63) ≤ N := Nat.le_of_dvd (by omega) hdiv
    have hpow : 2 ^ 63 ≤ 2 ^ (f * 63) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : (2 : ℕ) ^ 63 ≤ 174182400 := le_trans (le_trans hpow hle) hN
    norm_num at this

private lemma ggSpLayerOrd_eq_360 {m f : ℕ} (h : ggSpLayerOrd m (2 ^ f) = 360) :
    m = 2 ∧ f = 1 := by
  by_cases hsp : m = 2 ∧ 2 ^ f = 2
  · obtain ⟨hm, hq⟩ := hsp
    refine ⟨hm, ?_⟩
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) (by simpa using hq)
  · have hbc : ordBC m (2 ^ f) = 360 := by
      simpa [ggSpLayerOrd, hsp] using h
    exact (ordBC_ne_360 hbc).elim

private lemma ggSpLayerOrd_eq_60 {m f : ℕ} (h : ggSpLayerOrd m (2 ^ f) = 60) :
    m = 1 ∧ f = 2 := by
  by_cases hsp : m = 2 ∧ 2 ^ f = 2
  · have h360 : ggSpLayerOrd m (2 ^ f) = 360 := by simp [ggSpLayerOrd, hsp]
    rw [h360] at h
    omega
  · have hbc : ordBC m (2 ^ f) = 60 := by
      simpa [ggSpLayerOrd, hsp] using h
    exact ordBC_eq_60 hbc

private lemma ggSpLayerOrd_eq_ordBC_of_ne_360 {m f N : ℕ} (hN : N ≠ 360)
    (h : ggSpLayerOrd m (2 ^ f) = N) : ordBC m (2 ^ f) = N := by
  by_cases hsp : m = 2 ∧ 2 ^ f = 2
  · have h360 : ggSpLayerOrd m (2 ^ f) = 360 := by simp [ggSpLayerOrd, hsp]
    rw [h360] at h
    omega
  · simpa [ggSpLayerOrd, hsp] using h

theorem ggRootFactorOrders_two_le_count_sixty {t : CFSG.Open.StatedLieTag} {n f : ℕ}
    {o : List ℕ} (ho : o ∈ ggRootFactorOrders t n f) (h : 2 ≤ o.count 60) :
    (t = .PSp ∧ n = 3 ∧ f = 2) ∨ (t = .POmegaPlus ∧ n = 4 ∧ f = 2) := by
  cases t with
  | PSL =>
    simp only [ggRootFactorOrders, List.mem_singleton] at ho
    subst o
    have h1 : [ordA (n - 3) (2 ^ f)].count 60 ≤ 1 := by
      simpa using List.count_le_length (a := 60) (l := [ordA (n - 3) (2 ^ f)])
    omega
  | PSU =>
    simp only [ggRootFactorOrders, List.mem_singleton] at ho
    subst o
    have h1 : [ordTwistedA (n - 3) (2 ^ f)].count 60 ≤ 1 := by
      simpa using List.count_le_length (a := 60) (l := [ordTwistedA (n - 3) (2 ^ f)])
    omega
  | PSp =>
    simp only [ggRootFactorOrders, List.mem_cons, List.mem_singleton, List.not_mem_nil,
      or_false, false_or] at ho
    split_ifs at ho with hn2
    · rcases ho with rfl | rfl
      · have hlen : [ggSpLayerOrd (n - 1) (2 ^ f)].count 60 ≤ 1 := by
          simpa using List.count_le_length (a := 60) (l := [ggSpLayerOrd (n - 1) (2 ^ f)])
        omega
      · have hlen : [ordA 1 (2 ^ f)].count 60 ≤ 1 := by
          simpa using List.count_le_length (a := 60) (l := [ordA 1 (2 ^ f)])
        omega
    · rcases ho with rfl | rfl
      · have hlen : [ggSpLayerOrd (n - 1) (2 ^ f)].count 60 ≤ 1 := by
          simpa using List.count_le_length (a := 60) (l := [ggSpLayerOrd (n - 1) (2 ^ f)])
        omega
      · have ha : ordA 1 (2 ^ f) = 60 := by
          by_contra ha
          simp [List.count_cons, ha] at h
          split_ifs at h <;> omega
        have hb : ggSpLayerOrd (n - 2) (2 ^ f) = 60 := by
          by_contra hb
          simp [List.count_cons, ha, hb] at h
        obtain ⟨hm, hf⟩ := ggSpLayerOrd_eq_60 hb
        obtain ⟨-, hf2⟩ := ordA_eq_60 ha
        left
        exact ⟨rfl, by omega, hf2⟩
  | POmegaOdd => simp [ggRootFactorOrders] at ho
  | POmegaPlus =>
    simp only [ggRootFactorOrders] at ho
    split_ifs at ho with hn4
    · simp only [List.mem_singleton] at ho
      subst o
      have ha : ordA 1 (2 ^ f) = 60 := by
        by_contra ha
        simp [List.count_cons, ha] at h
      obtain ⟨-, hf⟩ := ordA_eq_60 ha
      right
      exact ⟨rfl, hn4, hf⟩
    · simp only [List.mem_singleton] at ho
      subst o
      have ha : ordA 1 (2 ^ f) = 60 := by
        by_contra ha
        simp [List.count_cons, ha] at h
        split_ifs at h <;> omega
      have hb : ordD (n - 2) (2 ^ f) = 60 := by
        by_contra hb
        simp [List.count_cons, ha, hb] at h
      obtain ⟨-, hf⟩ := ordA_eq_60 ha
      subst hf
      exact (ordD_ne_60 hb).elim
  | POmegaMinus =>
    simp only [ggRootFactorOrders, List.mem_singleton] at ho
    subst o
    have ha : ordA 1 (2 ^ f) = 60 := by
      by_contra ha
      simp [List.count_cons, ha] at h
      split_ifs at h <;> omega
    have hb : ordTwistedD (n - 2) (2 ^ f) = 60 := by
      by_contra hb
      simp [List.count_cons, ha, hb] at h
    obtain ⟨-, hf⟩ := ordA_eq_60 ha
    subst hf
    obtain ⟨-, hf'⟩ := ordTwistedD_eq_60 hb
    omega
  | G2 => simp [ggRootFactorOrders] at ho
  | F4 =>
    simp only [ggRootFactorOrders, List.mem_singleton] at ho
    subst o
    have h1 : [ordBC 3 (2 ^ f)].count 60 ≤ 1 := by
      simpa using List.count_le_length (a := 60) (l := [ordBC 3 (2 ^ f)])
    omega
  | E6 =>
    simp only [ggRootFactorOrders, List.mem_singleton] at ho
    subst o
    have h1 : [ordA 5 (2 ^ f)].count 60 ≤ 1 := by
      simpa using List.count_le_length (a := 60) (l := [ordA 5 (2 ^ f)])
    omega
  | E7 =>
    simp only [ggRootFactorOrders, List.mem_singleton] at ho
    subst o
    have h1 : [ordD 6 (2 ^ f)].count 60 ≤ 1 := by
      simpa using List.count_le_length (a := 60) (l := [ordD 6 (2 ^ f)])
    omega
  | E8 =>
    simp only [ggRootFactorOrders, List.mem_singleton] at ho
    subst o
    have h1 : [ordE7 (2 ^ f)].count 60 ≤ 1 := by
      simpa using List.count_le_length (a := 60) (l := [ordE7 (2 ^ f)])
    omega
  | twistedE6 =>
    simp only [ggRootFactorOrders, List.mem_singleton] at ho
    subst o
    have h1 : [ordTwistedA 5 (2 ^ f)].count 60 ≤ 1 := by
      simpa using List.count_le_length (a := 60) (l := [ordTwistedA 5 (2 ^ f)])
    omega
  | trialityD4 => simp [ggRootFactorOrders] at ho
  | twistedB2 => simp [ggRootFactorOrders] at ho
  | twistedG2 => simp [ggRootFactorOrders] at ho
  | twistedF4 => simp [ggRootFactorOrders] at ho
  | Tits => simp [ggRootFactorOrders] at ho

theorem ggRootFactorOrders_mem_360 {t : CFSG.Open.StatedLieTag} {n f : ℕ} {o : List ℕ}
    (ho : o ∈ ggRootFactorOrders t n f) (h : 360 ∈ o) :
    t = .PSp ∧ (n = 3 ∨ n = 4) ∧ f = 1 := by
  cases t with
  | PSL =>
    simp only [ggRootFactorOrders, List.mem_singleton] at ho
    subst o
    simp only [List.mem_singleton] at h
    exact (ordA_ne_360 h.symm).elim
  | PSU =>
    simp only [ggRootFactorOrders, List.mem_singleton] at ho
    subst o
    simp only [List.mem_singleton] at h
    exact (ordTwistedA_ne_360 h.symm).elim
  | PSp =>
    simp only [ggRootFactorOrders, List.mem_cons, List.mem_singleton, List.not_mem_nil,
      or_false, false_or] at ho
    split_ifs at ho with hn2
    · rcases ho with rfl | rfl
      · simp only [List.mem_singleton] at h
        obtain ⟨hm, hf⟩ := ggSpLayerOrd_eq_360 h.symm
        exact ⟨rfl, by omega, hf⟩
      · simp only [List.mem_singleton] at h
        exact (ordA_ne_360 h.symm).elim
    · rcases ho with rfl | rfl
      · simp only [List.mem_singleton] at h
        obtain ⟨hm, hf⟩ := ggSpLayerOrd_eq_360 h.symm
        exact ⟨rfl, by omega, hf⟩
      · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
          false_or] at h
        rcases h with h | h
        · exact (ordA_ne_360 h.symm).elim
        · obtain ⟨hm, hf⟩ := ggSpLayerOrd_eq_360 h.symm
          exact ⟨rfl, by omega, hf⟩
  | POmegaOdd => simp [ggRootFactorOrders] at ho
  | POmegaPlus =>
    simp only [ggRootFactorOrders] at ho
    split_ifs at ho with hn4
    · simp only [List.mem_singleton] at ho
      subst o
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
        false_or] at h
      rcases h with h | h | h
      · exact (ordA_ne_360 h.symm).elim
      · exact (ordA_ne_360 h.symm).elim
      · exact (ordA_ne_360 h.symm).elim
    · simp only [List.mem_singleton] at ho
      subst o
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
        false_or] at h
      rcases h with h | h
      · exact (ordA_ne_360 h.symm).elim
      · exact (ordD_ne_360 h.symm).elim
  | POmegaMinus =>
    simp only [ggRootFactorOrders, List.mem_singleton] at ho
    subst o
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
      false_or] at h
    rcases h with h | h
    · exact (ordA_ne_360 h.symm).elim
    · exact (ordTwistedD_ne_360 h.symm).elim
  | G2 => simp [ggRootFactorOrders] at ho
  | F4 =>
    simp only [ggRootFactorOrders, List.mem_singleton] at ho
    subst o
    simp only [List.mem_singleton] at h
    exact (ordBC_ne_360 h.symm).elim
  | E6 =>
    simp only [ggRootFactorOrders, List.mem_singleton] at ho
    subst o
    simp only [List.mem_singleton] at h
    exact (ordA_ne_360 h.symm).elim
  | E7 =>
    simp only [ggRootFactorOrders, List.mem_singleton] at ho
    subst o
    simp only [List.mem_singleton] at h
    exact (ordD_ne_360 h.symm).elim
  | E8 =>
    simp only [ggRootFactorOrders, List.mem_singleton] at ho
    subst o
    simp only [List.mem_singleton] at h
    exact (ordE7_ne (by norm_num) (by norm_num) h.symm).elim
  | twistedE6 =>
    simp only [ggRootFactorOrders, List.mem_singleton] at ho
    subst o
    simp only [List.mem_singleton] at h
    exact (ordTwistedA_ne_360 h.symm).elim
  | trialityD4 => simp [ggRootFactorOrders] at ho
  | twistedB2 => simp [ggRootFactorOrders] at ho
  | twistedG2 => simp [ggRootFactorOrders] at ho
  | twistedF4 => simp [ggRootFactorOrders] at ho
  | Tits => simp [ggRootFactorOrders] at ho

theorem ggRootFactorOrders_mem_174182400 {t : CFSG.Open.StatedLieTag} {n f : ℕ} {o : List ℕ}
    (ho : o ∈ ggRootFactorOrders t n f) (h : 174182400 ∈ o) :
    t = .POmegaPlus ∧ n = 6 ∧ f = 1 := by
  cases t with
  | PSL =>
    simp only [ggRootFactorOrders, List.mem_singleton] at ho
    subst o
    simp only [List.mem_singleton] at h
    exact (ordA_ne_174182400 h.symm).elim
  | PSU =>
    simp only [ggRootFactorOrders, List.mem_singleton] at ho
    subst o
    simp only [List.mem_singleton] at h
    exact (ordTwistedA_ne_174182400 h.symm).elim
  | PSp =>
    simp only [ggRootFactorOrders, List.mem_cons, List.mem_singleton, List.not_mem_nil,
      or_false, false_or] at ho
    split_ifs at ho with hn2
    · rcases ho with rfl | rfl
      · simp only [List.mem_singleton] at h
        have hbc : ordBC (n - 1) (2 ^ f) = 174182400 :=
          ggSpLayerOrd_eq_ordBC_of_ne_360 (by norm_num) h.symm
        exact (ordBC_ne_174182400 hbc).elim
      · simp only [List.mem_singleton] at h
        exact (ordA_ne_174182400 h.symm).elim
    · rcases ho with rfl | rfl
      · simp only [List.mem_singleton] at h
        have hbc : ordBC (n - 1) (2 ^ f) = 174182400 :=
          ggSpLayerOrd_eq_ordBC_of_ne_360 (by norm_num) h.symm
        exact (ordBC_ne_174182400 hbc).elim
      · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
          false_or] at h
        rcases h with h | h
        · exact (ordA_ne_174182400 h.symm).elim
        · have hbc : ordBC (n - 2) (2 ^ f) = 174182400 :=
            ggSpLayerOrd_eq_ordBC_of_ne_360 (by norm_num) h.symm
          exact (ordBC_ne_174182400 hbc).elim
  | POmegaOdd => simp [ggRootFactorOrders] at ho
  | POmegaPlus =>
    simp only [ggRootFactorOrders] at ho
    split_ifs at ho with hn4
    · simp only [List.mem_singleton] at ho
      subst o
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
        false_or] at h
      rcases h with h | h | h
      · exact (ordA_ne_174182400 h.symm).elim
      · exact (ordA_ne_174182400 h.symm).elim
      · exact (ordA_ne_174182400 h.symm).elim
    · simp only [List.mem_singleton] at ho
      subst o
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
        false_or] at h
      rcases h with h | h
      · exact (ordA_ne_174182400 h.symm).elim
      · obtain ⟨hk, hf⟩ := ordD_eq_174182400 h.symm
        exact ⟨rfl, by omega, hf⟩
  | POmegaMinus =>
    simp only [ggRootFactorOrders, List.mem_singleton] at ho
    subst o
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
      false_or] at h
    rcases h with h | h
    · exact (ordA_ne_174182400 h.symm).elim
    · exact (ordTwistedD_ne_174182400 h.symm).elim
  | G2 => simp [ggRootFactorOrders] at ho
  | F4 =>
    simp only [ggRootFactorOrders, List.mem_singleton] at ho
    subst o
    simp only [List.mem_singleton] at h
    exact (ordBC_ne_174182400 h.symm).elim
  | E6 =>
    simp only [ggRootFactorOrders, List.mem_singleton] at ho
    subst o
    simp only [List.mem_singleton] at h
    exact (ordA_ne_174182400 h.symm).elim
  | E7 =>
    simp only [ggRootFactorOrders, List.mem_singleton] at ho
    subst o
    simp only [List.mem_singleton] at h
    obtain ⟨hk, -⟩ := ordD_eq_174182400 h.symm
    omega
  | E8 =>
    simp only [ggRootFactorOrders, List.mem_singleton] at ho
    subst o
    simp only [List.mem_singleton] at h
    exact (ordE7_ne (by norm_num) (by norm_num) h.symm).elim
  | twistedE6 =>
    simp only [ggRootFactorOrders, List.mem_singleton] at ho
    subst o
    simp only [List.mem_singleton] at h
    exact (ordTwistedA_ne_174182400 h.symm).elim
  | trialityD4 => simp [ggRootFactorOrders] at ho
  | twistedB2 => simp [ggRootFactorOrders] at ho
  | twistedG2 => simp [ggRootFactorOrders] at ho
  | twistedF4 => simp [ggRootFactorOrders] at ho
  | Tits => simp [ggRootFactorOrders] at ho

theorem ggRootFactorOrders_mem_25920 {t : CFSG.Open.StatedLieTag} {n f : ℕ} {o : List ℕ}
    (ho : o ∈ ggRootFactorOrders t n f) (h : 25920 ∈ o) :
    (t = .PSU ∧ n = 6 ∧ f = 1) ∨ (t = .POmegaMinus ∧ n = 5 ∧ f = 1) := by
  cases t with
  | PSL =>
    simp only [ggRootFactorOrders, List.mem_singleton] at ho
    subst o
    simp only [List.mem_singleton] at h
    exact (ordA_ne_25920 h.symm).elim
  | PSU =>
    simp only [ggRootFactorOrders, List.mem_singleton] at ho
    subst o
    simp only [List.mem_singleton] at h
    obtain ⟨hk, hf⟩ := ordTwistedA_eq_25920 h.symm
    left
    exact ⟨rfl, by omega, hf⟩
  | PSp =>
    simp only [ggRootFactorOrders, List.mem_cons, List.mem_singleton, List.not_mem_nil,
      or_false, false_or] at ho
    split_ifs at ho with hn2
    · rcases ho with rfl | rfl
      · simp only [List.mem_singleton] at h
        have hbc : ordBC (n - 1) (2 ^ f) = 25920 :=
          ggSpLayerOrd_eq_ordBC_of_ne_360 (by norm_num) h.symm
        exact (ordBC_ne_25920 hbc).elim
      · simp only [List.mem_singleton] at h
        exact (ordA_ne_25920 h.symm).elim
    · rcases ho with rfl | rfl
      · simp only [List.mem_singleton] at h
        have hbc : ordBC (n - 1) (2 ^ f) = 25920 :=
          ggSpLayerOrd_eq_ordBC_of_ne_360 (by norm_num) h.symm
        exact (ordBC_ne_25920 hbc).elim
      · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
          false_or] at h
        rcases h with h | h
        · exact (ordA_ne_25920 h.symm).elim
        · have hbc : ordBC (n - 2) (2 ^ f) = 25920 :=
            ggSpLayerOrd_eq_ordBC_of_ne_360 (by norm_num) h.symm
          exact (ordBC_ne_25920 hbc).elim
  | POmegaOdd => simp [ggRootFactorOrders] at ho
  | POmegaPlus =>
    simp only [ggRootFactorOrders] at ho
    split_ifs at ho with hn4
    · simp only [List.mem_singleton] at ho
      subst o
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
        false_or] at h
      rcases h with h | h | h
      · exact (ordA_ne_25920 h.symm).elim
      · exact (ordA_ne_25920 h.symm).elim
      · exact (ordA_ne_25920 h.symm).elim
    · simp only [List.mem_singleton] at ho
      subst o
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
        false_or] at h
      rcases h with h | h
      · exact (ordA_ne_25920 h.symm).elim
      · exact (ordD_ne_25920 h.symm).elim
  | POmegaMinus =>
    simp only [ggRootFactorOrders, List.mem_singleton] at ho
    subst o
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
      false_or] at h
    rcases h with h | h
    · exact (ordA_ne_25920 h.symm).elim
    · obtain ⟨hk, hf⟩ := ordTwistedD_eq_25920 h.symm
      right
      exact ⟨rfl, by omega, hf⟩
  | G2 => simp [ggRootFactorOrders] at ho
  | F4 =>
    simp only [ggRootFactorOrders, List.mem_singleton] at ho
    subst o
    simp only [List.mem_singleton] at h
    exact (ordBC_ne_25920 h.symm).elim
  | E6 =>
    simp only [ggRootFactorOrders, List.mem_singleton] at ho
    subst o
    simp only [List.mem_singleton] at h
    exact (ordA_ne_25920 h.symm).elim
  | E7 =>
    simp only [ggRootFactorOrders, List.mem_singleton] at ho
    subst o
    simp only [List.mem_singleton] at h
    exact (ordD_ne_25920 h.symm).elim
  | E8 =>
    simp only [ggRootFactorOrders, List.mem_singleton] at ho
    subst o
    simp only [List.mem_singleton] at h
    exact (ordE7_ne (by norm_num) (by norm_num) h.symm).elim
  | twistedE6 =>
    simp only [ggRootFactorOrders, List.mem_singleton] at ho
    subst o
    simp only [List.mem_singleton] at h
    obtain ⟨hk, -⟩ := ordTwistedA_eq_25920 h.symm
    omega
  | trialityD4 => simp [ggRootFactorOrders] at ho
  | twistedB2 => simp [ggRootFactorOrders] at ho
  | twistedG2 => simp [ggRootFactorOrders] at ho
  | twistedF4 => simp [ggRootFactorOrders] at ho
  | Tits => simp [ggRootFactorOrders] at ho

end CFSG.StandardType
