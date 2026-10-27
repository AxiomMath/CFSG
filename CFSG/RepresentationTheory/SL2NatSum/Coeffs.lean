module

public import CFSG.RepresentationTheory.SL2NatSum.Interpolation
public import CFSG.RepresentationTheory.SL2NatSum.ChooseTwo

public section

namespace CFSG.RepresentationTheory.SL2NatSum

variable {K : Type*} [Field K] [Fintype K] [CharP K 2] {R : Type*} [Ring R] [Algebra K R]

theorem coeff_shift {P : K → R} {W : ℕ → R} (h : R) (s : K)
    (hW : ∀ x, P x = ∑ j ∈ Finset.range (Fintype.card K), x ^ j • W j)
    (hh : ∀ x, h * P x = P (s * x) * h) :
    ∀ j < Fintype.card K, h * W j = s ^ j • (W j * h) := by
  intro j hj
  have hzero : ∀ x : K,
      ∑ k ∈ Finset.range (Fintype.card K),
        x ^ k • (h * W k - s ^ k • (W k * h)) = 0 := by
    intro x
    have h1 : (∑ k ∈ Finset.range (Fintype.card K), x ^ k • (h * W k)) = h * P x := by
      rw [hW x, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_smul_comm]
    have h2 : (∑ k ∈ Finset.range (Fintype.card K),
          x ^ k • (s ^ k • (W k * h))) = P (s * x) * h := by
      rw [hW (s * x), Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_smul, mul_comm (x ^ k) (s ^ k), ← mul_pow, smul_mul_assoc]
    calc
      (∑ k ∈ Finset.range (Fintype.card K),
          x ^ k • (h * W k - s ^ k • (W k * h)))
          = ∑ k ∈ Finset.range (Fintype.card K),
              (x ^ k • (h * W k) - x ^ k • (s ^ k • (W k * h))) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [smul_sub]
      _ = (∑ k ∈ Finset.range (Fintype.card K), x ^ k • (h * W k))
            - ∑ k ∈ Finset.range (Fintype.card K), x ^ k • (s ^ k • (W k * h)) := by
            rw [Finset.sum_sub_distrib]
      _ = h * P x - P (s * x) * h := by rw [h1, h2]
      _ = 0 := by rw [hh x, sub_self]
  exact sub_eq_zero.mp (coeff_eq_zero_of_forall_sum_eq_zero
    (fun k => h * W k - s ^ k • (W k * h)) hzero j hj)

private lemma sum_smul_ite_eq_zero_right {P : K → R} {W : ℕ → R}
    (hW : ∀ x, P x = ∑ j ∈ Finset.range (Fintype.card K), x ^ j • W j) (x y : K) :
    (∑ i ∈ Finset.range (Fintype.card K), ∑ k ∈ Finset.range (Fintype.card K),
        x ^ i • y ^ k • (if k = 0 then W i else 0)) = P x := by
  have hq0 : 0 < Fintype.card K := Fintype.card_pos
  calc
    (∑ i ∈ Finset.range (Fintype.card K), ∑ k ∈ Finset.range (Fintype.card K),
        x ^ i • y ^ k • (if k = 0 then W i else 0))
        = ∑ i ∈ Finset.range (Fintype.card K), x ^ i • W i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_eq_single 0 (fun k _ hk => by simp [hk])
            (fun h => absurd (Finset.mem_range.mpr hq0) h)]
          simp
    _ = P x := (hW x).symm

private lemma sum_smul_ite_eq_zero_left {P : K → R} {W : ℕ → R}
    (hW : ∀ x, P x = ∑ j ∈ Finset.range (Fintype.card K), x ^ j • W j) (x y : K) :
    (∑ i ∈ Finset.range (Fintype.card K), ∑ k ∈ Finset.range (Fintype.card K),
        x ^ i • y ^ k • (if i = 0 then W k else 0)) = P y := by
  have hq0 : 0 < Fintype.card K := Fintype.card_pos
  calc
    (∑ i ∈ Finset.range (Fintype.card K), ∑ k ∈ Finset.range (Fintype.card K),
        x ^ i • y ^ k • (if i = 0 then W k else 0))
        = ∑ k ∈ Finset.range (Fintype.card K), y ^ k • W k := by
          rw [Finset.sum_eq_single 0 (fun i _ hi => by simp [hi])
            (fun h => absurd (Finset.mem_range.mpr hq0) h)]
          simp
    _ = P y := (hW y).symm

private lemma sum_smul_mul_coeff {P : K → R} {W : ℕ → R}
    (hW : ∀ x, P x = ∑ j ∈ Finset.range (Fintype.card K), x ^ j • W j) (x y : K) :
    (∑ i ∈ Finset.range (Fintype.card K), ∑ k ∈ Finset.range (Fintype.card K),
        x ^ i • y ^ k • (W i * W k)) = P x * P y := by
  rw [hW x, hW y, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_mul_smul_comm, smul_smul]

private lemma sum_pow_smul_eq_sum_choose (x y : K) (W : ℕ → R) :
    (∑ j ∈ Finset.range (Fintype.card K), (x + y) ^ j • W j) =
      ∑ i ∈ Finset.range (Fintype.card K), ∑ k ∈ Finset.range (Fintype.card K),
        x ^ i • y ^ k •
          (if i + k < Fintype.card K then ((i + k).choose i : K) • W (i + k) else 0) := by
  classical
  let f : ℕ → ℕ → R := fun i j => x ^ i • y ^ (j - i) • ((j.choose i : K) • W j)
  have step1 : (∑ j ∈ Finset.range (Fintype.card K), (x + y) ^ j • W j) =
      ∑ j ∈ Finset.range (Fintype.card K),
        ∑ i ∈ Finset.range (j + 1), f i j := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [add_pow, Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [f, smul_smul, mul_assoc]
  have step2 : (∑ j ∈ Finset.range (Fintype.card K),
        ∑ i ∈ Finset.range (j + 1), f i j) =
      ∑ i ∈ Finset.range (Fintype.card K),
        ∑ j ∈ Finset.Ico i (Fintype.card K), f i j := by
    simp only [Finset.range_eq_Ico]
    exact (Finset.sum_Ico_Ico_comm 0 (Fintype.card K) f).symm
  have step3 : (∑ i ∈ Finset.range (Fintype.card K),
        ∑ j ∈ Finset.Ico i (Fintype.card K), f i j) =
      ∑ i ∈ Finset.range (Fintype.card K),
        ∑ k ∈ Finset.range (Fintype.card K - i), f i (i + k) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_Ico_eq_sum_range]
  have step4 : (∑ i ∈ Finset.range (Fintype.card K),
        ∑ k ∈ Finset.range (Fintype.card K - i), f i (i + k)) =
      ∑ i ∈ Finset.range (Fintype.card K), ∑ k ∈ Finset.range (Fintype.card K),
        x ^ i • y ^ k •
          (if i + k < Fintype.card K then ((i + k).choose i : K) • W (i + k) else 0) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    have hfilter : (Finset.range (Fintype.card K)).filter
        (fun k => k < Fintype.card K - i) = Finset.range (Fintype.card K - i) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    calc
      (∑ k ∈ Finset.range (Fintype.card K - i), f i (i + k))
          = ∑ k ∈ (Finset.range (Fintype.card K)).filter
              (fun k => k < Fintype.card K - i), f i (i + k) := by
            rw [hfilter]
      _ = ∑ k ∈ Finset.range (Fintype.card K),
            (if k < Fintype.card K - i then f i (i + k) else 0) := by
            rw [Finset.sum_filter]
      _ = ∑ k ∈ Finset.range (Fintype.card K),
            x ^ i • y ^ k •
              (if i + k < Fintype.card K then
                ((i + k).choose i : K) • W (i + k) else 0) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            have hiff : k < Fintype.card K - i ↔ i + k < Fintype.card K := by
              rw [Nat.lt_sub_iff_add_lt]
              omega
            by_cases hk : k < Fintype.card K - i
            · rw [if_pos hk, if_pos (hiff.mp hk)]
              simp only [f, Nat.add_sub_cancel_left]
            · rw [if_neg hk, if_neg (hiff.not.mp hk)]
              simp
  rw [step1, step2, step3, step4]

theorem coeff_mul {n : ℕ} (hq : Fintype.card K = 2 ^ n) {P : K → R} {W : ℕ → R}
    (hW : ∀ x, P x = ∑ j ∈ Finset.range (Fintype.card K), x ^ j • W j)
    (hPadd : ∀ x y, P (x + y) = P x + P y + P x * P y) :
    ∀ i < Fintype.card K, ∀ k < Fintype.card K, 0 < i → 0 < k →
      W i * W k = if i &&& k = 0 then W (i + k) else 0 := by
  classical
  let c : ℕ → ℕ → R := fun a b =>
    (if a + b < Fintype.card K then ((a + b).choose a : K) • W (a + b) else 0)
      - (if b = 0 then W a else 0) - (if a = 0 then W b else 0) - W a * W b
  have hc : ∀ a < Fintype.card K, ∀ b < Fintype.card K, c a b = 0 := by
    apply coeff₂_eq_zero_of_forall_sum_eq_zero c
    intro x y
    have hbin : (∑ i ∈ Finset.range (Fintype.card K),
        ∑ k ∈ Finset.range (Fintype.card K),
          x ^ i • y ^ k •
            (if i + k < Fintype.card K then ((i + k).choose i : K) • W (i + k) else 0))
        = P (x + y) := (sum_pow_smul_eq_sum_choose x y W).symm.trans (hW (x + y)).symm
    have h1 := sum_smul_ite_eq_zero_right hW x y
    have h2 := sum_smul_ite_eq_zero_left hW x y
    have h3 := sum_smul_mul_coeff hW x y
    calc
      (∑ a ∈ Finset.range (Fintype.card K), ∑ b ∈ Finset.range (Fintype.card K),
          x ^ a • y ^ b • c a b)
          = (∑ a ∈ Finset.range (Fintype.card K), ∑ b ∈ Finset.range (Fintype.card K),
                x ^ a • y ^ b •
                  (if a + b < Fintype.card K then
                    ((a + b).choose a : K) • W (a + b) else 0))
            - (∑ a ∈ Finset.range (Fintype.card K), ∑ b ∈ Finset.range (Fintype.card K),
                x ^ a • y ^ b • (if b = 0 then W a else 0))
            - (∑ a ∈ Finset.range (Fintype.card K), ∑ b ∈ Finset.range (Fintype.card K),
                x ^ a • y ^ b • (if a = 0 then W b else 0))
            - (∑ a ∈ Finset.range (Fintype.card K), ∑ b ∈ Finset.range (Fintype.card K),
                x ^ a • y ^ b • (W a * W b)) := by
            simp only [c, smul_sub, Finset.sum_sub_distrib]
      _ = P (x + y) - P x - P y - P x * P y := by rw [hbin, h1, h2, h3]
      _ = 0 := by rw [hPadd x y]; abel
  intro i hi k hk hi0 hk0
  have hci : c i k = 0 := hc i hi k hk
  have hmain : W i * W k =
      if i + k < Fintype.card K then ((i + k).choose i : K) • W (i + k) else 0 := by
    simp only [c] at hci
    rw [if_neg (by omega : ¬ k = 0), if_neg (by omega : ¬ i = 0)] at hci
    simp only [sub_zero] at hci
    exact (sub_eq_zero.mp hci).symm
  by_cases hik : i &&& k = 0
  · have hodd : Odd ((i + k).choose i) := (odd_choose_add_iff i k).mpr hik
    have hcoef : ((i + k).choose i : K) = 1 := by
      rw [CharTwo.natCast_eq_ite, if_neg (Nat.not_even_iff_odd.mpr hodd)]
    have hsum : i + k = i ||| k := add_eq_or_of_and_eq_zero hik
    have hilt : i + k < Fintype.card K := by
      have hi2 : i < 2 ^ n := by rwa [hq] at hi
      have hk2 : k < 2 ^ n := by rwa [hq] at hk
      rw [hq, hsum]
      exact Nat.or_lt_two_pow hi2 hk2
    rw [if_pos hik, hmain, if_pos hilt, hcoef, one_smul]
  · have hnotodd : ¬ Odd ((i + k).choose i) := (odd_choose_add_iff i k).not.mpr hik
    have heven : Even ((i + k).choose i) := Nat.not_odd_iff_even.mp hnotodd
    have hcoef : ((i + k).choose i : K) = 0 := by
      rw [CharTwo.natCast_eq_ite, if_pos heven]
    rw [if_neg hik, hmain]
    by_cases hilt : i + k < Fintype.card K
    · rw [if_pos hilt, hcoef, zero_smul]
    · rw [if_neg hilt]

theorem coeff_pow_two_comm {n : ℕ} (hq : Fintype.card K = 2 ^ n) {P : K → R} {W : ℕ → R}
    (hW : ∀ x, P x = ∑ j ∈ Finset.range (Fintype.card K), x ^ j • W j)
    (hPadd : ∀ x y, P (x + y) = P x + P y + P x * P y) :
    ∀ b < n, ∀ c < n, W (2 ^ b) * W (2 ^ c) = W (2 ^ c) * W (2 ^ b) := by
  intro b hb c hc
  by_cases hbc : b = c
  · subst hbc
    rfl
  have hand : 2 ^ b &&& 2 ^ c = 0 := by
    rw [Nat.and_two_pow, Nat.testBit_two_pow, decide_eq_false hbc]
    simp
  have hand' : 2 ^ c &&& 2 ^ b = 0 := by
    rw [Nat.and_two_pow, Nat.testBit_two_pow, decide_eq_false (Ne.symm hbc)]
    simp
  have hbq : 2 ^ b < Fintype.card K := by
    rw [hq]
    exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mpr hb
  have hcq : 2 ^ c < Fintype.card K := by
    rw [hq]
    exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mpr hc
  have hbpos : 0 < 2 ^ b := Nat.pow_pos (by norm_num)
  have hcpos : 0 < 2 ^ c := Nat.pow_pos (by norm_num)
  have hbcprod := coeff_mul hq hW hPadd (2 ^ b) hbq (2 ^ c) hcq hbpos hcpos
  have hcbprod := coeff_mul hq hW hPadd (2 ^ c) hcq (2 ^ b) hbq hcpos hbpos
  rw [if_pos hand] at hbcprod
  rw [if_pos hand'] at hcbprod
  rw [hbcprod, hcbprod, add_comm]

theorem coeff_eq_zero_of_not_pow_two {n : ℕ} (hq : Fintype.card K = 2 ^ n) (W : ℕ → R)
    (hprod : ∀ i < Fintype.card K, ∀ k < Fintype.card K, 0 < i → 0 < k →
      W i * W k = if i &&& k = 0 then W (i + k) else 0)
    (hway : ∀ b < n, ∀ c < n, b ≠ c → W (2 ^ b) * W (2 ^ c) = 0) :
    ∀ j < 2 ^ n, 0 < j → (¬ ∃ c, j = 2 ^ c) → W j = 0 := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hjq hj0 hjpow
    obtain ⟨b, m, hm_odd, hjm⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.pos_iff_ne_zero.mp hj0)
    obtain ⟨t, rfl⟩ := hm_odd
    have hm_ne1 : 2 * t + 1 ≠ 1 := by
      intro h
      exact hjpow ⟨b, by rw [hjm, h, mul_one]⟩
    have ht : 0 < t := by omega
    have hb_le_j : 2 ^ b ≤ j := by
      rw [hjm]
      exact Nat.le_mul_of_pos_right _ (by omega : 0 < 2 * t + 1)
    set k : ℕ := j - 2 ^ b with hk_def
    have hk_eq : k = 2 ^ (b + 1) * t := by
      rw [hk_def, Nat.sub_eq_iff_eq_add hb_le_j, hjm, pow_succ]
      ring
    have hk_pos : 0 < k := by
      rw [hk_eq]
      exact Nat.mul_pos (Nat.pow_pos (by norm_num)) ht
    have hk_lt_j : k < j := by
      rw [hk_def]
      exact Nat.sub_lt_of_pos_le (Nat.pow_pos (by norm_num)) hb_le_j
    have hk_lt_pow : k < 2 ^ n := lt_trans hk_lt_j hjq
    have hb_lt_n : b < n := by
      have h2b_lt : 2 ^ b < 2 ^ n := lt_of_le_of_lt hb_le_j hjq
      exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h2b_lt
    have h2b_lt_card : 2 ^ b < Fintype.card K := by rw [hq]; exact lt_of_le_of_lt hb_le_j hjq
    have hk_lt_card : k < Fintype.card K := by rw [hq]; exact hk_lt_pow
    have hand : 2 ^ b &&& k = 0 := by
      rw [hk_eq, Nat.two_pow_and, Nat.testBit_two_pow_mul,
        decide_eq_false (by omega : ¬ b + 1 ≤ b)]
      simp
    have hprod_bk := hprod (2 ^ b) h2b_lt_card k hk_lt_card
      (Nat.pow_pos (by norm_num)) hk_pos
    rw [if_pos hand] at hprod_bk
    have hjk : 2 ^ b + k = j := by
      rw [hk_def]
      exact Nat.add_sub_of_le hb_le_j
    by_cases hkpow : ∃ c, k = 2 ^ c
    · obtain ⟨c, hc⟩ := hkpow
      have hc_lt_n : c < n := by
        have h2c_lt : 2 ^ c < 2 ^ n := by rwa [hc] at hk_lt_pow
        exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h2c_lt
      have h2bpos : 0 < 2 ^ b := Nat.pow_pos (by norm_num)
      have hk_gt : 2 ^ b < k := by
        rw [hk_eq, pow_succ]
        nlinarith [h2bpos, ht]
      have hcb : c ≠ b := by
        rintro rfl
        rw [hc] at hk_gt
        exact (lt_irrefl _ hk_gt)
      calc
        W j = W (2 ^ b + k) := by rw [hjk]
        _ = W (2 ^ b) * W k := hprod_bk.symm
        _ = 0 := by
            have hway_bc := hway b hb_lt_n c hc_lt_n (Ne.symm hcb)
            rwa [← hc] at hway_bc
    · calc
        W j = W (2 ^ b + k) := by rw [hjk]
        _ = W (2 ^ b) * W k := hprod_bk.symm
        _ = 0 := by rw [ih k hk_lt_j hk_lt_pow hk_pos hkpow, mul_zero]

theorem coeff_mul_eq_zero {n : ℕ} (hq : Fintype.card K = 2 ^ n) (W : ℕ → R)
    (hW0 : W 0 = 0)
    (hprod : ∀ i < Fintype.card K, ∀ k < Fintype.card K, 0 < i → 0 < k →
      W i * W k = if i &&& k = 0 then W (i + k) else 0)
    (hway : ∀ b < n, ∀ c < n, b ≠ c → W (2 ^ b) * W (2 ^ c) = 0) :
    ∀ i < Fintype.card K, ∀ k < Fintype.card K, W i * W k = 0 := by
  have hnotpow := coeff_eq_zero_of_not_pow_two hq W hprod hway
  intro i hi k hk
  by_cases hi0 : i = 0
  · subst hi0
    rw [hW0, zero_mul]
  by_cases hk0 : k = 0
  · subst hk0
    rw [hW0, mul_zero]
  have hi0' : 0 < i := Nat.pos_of_ne_zero hi0
  have hk0' : 0 < k := Nat.pos_of_ne_zero hk0
  by_cases hik : i &&& k = 0
  · have hsum : i + k = i ||| k := add_eq_or_of_and_eq_zero hik
    have hi2 : i < 2 ^ n := by rwa [hq] at hi
    have hk2 : k < 2 ^ n := by rwa [hq] at hk
    have hik_lt : i + k < Fintype.card K := by
      rw [hq, hsum]
      exact Nat.or_lt_two_pow hi2 hk2
    rw [hprod i hi k hk hi0' hk0', if_pos hik]
    have hik_not_pow : ¬ ∃ c, i + k = 2 ^ c := by
      rintro ⟨c, hc⟩
      have hi_lt : i < 2 ^ c := by omega
      have hk_lt : k < 2 ^ c := by omega
      have hor_lt : i ||| k < 2 ^ c := Nat.or_lt_two_pow hi_lt hk_lt
      rw [← hsum, hc] at hor_lt
      exact (lt_irrefl _ hor_lt)
    exact hnotpow (i + k) (by rwa [hq] at hik_lt) (by omega) hik_not_pow
  · rw [hprod i hi k hk hi0' hk0', if_neg hik]

theorem exists_coeff_unipotent {n : ℕ} (hq : Fintype.card K = 2 ^ n)
    (P : K → R) (hP0 : P 0 = 0) (hPadd : ∀ x y, P (x + y) = P x + P y + P x * P y)
    (h : R) (s : K) (hh : ∀ x, h * P x = P (s * x) * h) :
    ∃ W : ℕ → R, (∀ j < 2 ^ n, h * W j = s ^ j • (W j * h)) ∧
      (∀ b < n, ∀ c < n, W (2 ^ b) * W (2 ^ c) = W (2 ^ c) * W (2 ^ b)) ∧
      ((∀ b < n, ∀ c < n, b ≠ c → W (2 ^ b) * W (2 ^ c) = 0) → ∀ x y, P x * P y = 0) := by
  obtain ⟨W, hW0, hW⟩ := exists_coeff P hP0
  refine ⟨W, ?_, ?_, ?_⟩
  · intro j hj
    exact coeff_shift h s hW hh j (by rw [hq]; exact hj)
  · exact coeff_pow_two_comm hq hW hPadd
  · intro hway
    have hprod : ∀ i < Fintype.card K, ∀ k < Fintype.card K, 0 < i → 0 < k →
        W i * W k = if i &&& k = 0 then W (i + k) else 0 :=
      coeff_mul hq hW hPadd
    have hzero := coeff_mul_eq_zero hq W hW0 hprod hway
    intro x y
    rw [← sum_smul_mul_coeff hW x y]
    refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun k hk => ?_
    rw [hzero i (Finset.mem_range.mp hi) k (Finset.mem_range.mp hk)]
    simp

end CFSG.RepresentationTheory.SL2NatSum
