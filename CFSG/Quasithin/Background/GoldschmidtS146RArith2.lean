module

public import CFSG.Quasithin.Background.GoldschmidtS146RArithDefs
public import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

namespace CFSG.Quasithin.GoldS146R

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

section Profile

theorem ordL2_add_pow (m : ℕ) : ordL2 m + 2 ^ m = (2 ^ m) ^ 3 := by
  have h : 1 ≤ (2 ^ m) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  unfold ordL2
  zify [h]
  ring

theorem srcProfile_of_odd {N r : ℕ} (hr : Odd r) (h : 4 * r < 4 ^ N) :
    SrcProfile (2 ^ N * r) :=
  Or.inr (Or.inr (Or.inr ⟨N, r, hr, rfl, h⟩))

theorem four_mul_lt_pow {q a b i j k : ℕ} (hq : 4 ≤ q) (ha : a + 1 ≤ q ^ i)
    (hb : b + 1 ≤ q ^ j) (hk : i + j + 1 ≤ k) : 4 * (a * b) < q ^ k := by
  have h1 : (a + 1) * (b + 1) ≤ q ^ i * q ^ j := Nat.mul_le_mul ha hb
  have h2 : a * b < q ^ (i + j) := by
    rw [pow_add]
    nlinarith
  have h3 : 4 * q ^ (i + j) ≤ q ^ (i + j + 1) := by
    rw [pow_succ]
    nlinarith [Nat.zero_le (q ^ (i + j))]
  have h4 : q ^ (i + j + 1) ≤ q ^ k := Nat.pow_le_pow_right (by omega) hk
  omega

theorem four_mul_pow_le {q : ℕ} (k : ℕ) (hq : 4 ≤ q) : 4 * q ^ k ≤ q ^ (k + 1) :=
  calc 4 * q ^ k ≤ q * q ^ k := Nat.mul_le_mul_right _ hq
    _ = q ^ (k + 1) := (pow_succ' q k).symm

theorem pow_pow_two (n k : ℕ) : (2 ^ n) ^ k = 2 ^ (n * k) := (pow_mul 2 n k).symm

theorem four_pow_eq (n k : ℕ) : (4 : ℕ) ^ (n * k) = (2 ^ n) ^ (2 * k) := by
  rw [← pow_mul, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
  congr 1
  ring

theorem four_le_two_pow {n : ℕ} (hn : 2 ≤ n) : 4 ≤ 2 ^ n :=
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

theorem odd_two_pow_pow_sub_one' {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) : Odd ((2 ^ n) ^ k - 1) := by
  rw [pow_pow_two]
  have h : 2 ∣ 2 ^ (n * k) := dvd_pow_self 2 (by positivity)
  have h1 : 1 ≤ 2 ^ (n * k) := Nat.one_le_two_pow
  rw [Nat.odd_iff]
  omega

theorem odd_two_pow_pow_add_one' {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) : Odd ((2 ^ n) ^ k + 1) := by
  rw [pow_pow_two]
  have h : 2 ∣ 2 ^ (n * k) := dvd_pow_self 2 (by positivity)
  rw [Nat.odd_iff]
  omega

theorem srcProfile_ordL2 {m : ℕ} (hm : 2 ≤ m) : SrcProfile (ordL2 m) :=
  Or.inl ⟨m, hm, rfl⟩

theorem srcProfile_ordBC_two {n : ℕ} (hn : 2 ≤ n) : SrcProfile (ordBC 2 (2 ^ n)) := by
  have hq4 := four_le_two_pow hn
  have hodd1 : Odd (2 ^ n - 1) := by
    have h := odd_two_pow_pow_sub_one' (n := n) (k := 1) (by omega) le_rfl
    simpa using h
  have hgcd : Nat.gcd 2 (2 ^ n - 1) = 1 := Nat.coprime_two_left.mpr hodd1
  have heq : ordBC 2 (2 ^ n) = 2 ^ (n * 4) * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 4 - 1)) := by
    unfold ordBC
    rw [hgcd, Nat.div_one, show Finset.Icc 1 2 = {1, 2} by decide,
      Finset.prod_pair (by norm_num), ← pow_mul, show 2 * 2 = 4 by norm_num]
  rw [heq]
  refine srcProfile_of_odd (Odd.mul (odd_two_pow_pow_sub_one' (by omega) (by omega))
    (odd_two_pow_pow_sub_one' (by omega) (by omega))) ?_
  rw [four_pow_eq]
  refine four_mul_lt_pow (i := 2) (j := 4) hq4 ?_ ?_ (by norm_num)
  · have : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    omega
  · have : 1 ≤ (2 ^ n) ^ 4 := Nat.one_le_pow _ _ (by positivity)
    omega

theorem srcProfile_ordG2 {n : ℕ} (hn : 2 ≤ n) : SrcProfile (ordG2 (2 ^ n)) := by
  have hq4 := four_le_two_pow hn
  have heq : ordG2 (2 ^ n) = 2 ^ (n * 6) * (((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1)) := by
    unfold ordG2
    rw [← pow_mul, mul_assoc, mul_comm n 6]
  rw [heq]
  refine srcProfile_of_odd (Odd.mul (odd_two_pow_pow_sub_one' (by omega) (by omega))
    (odd_two_pow_pow_sub_one' (by omega) (by omega))) ?_
  rw [four_pow_eq]
  refine four_mul_lt_pow (i := 6) (j := 2) hq4 ?_ ?_ (by norm_num)
  · have : 1 ≤ (2 ^ n) ^ 6 := Nat.one_le_pow _ _ (by positivity)
    omega
  · have : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    omega

theorem ordA_two_eq (q : ℕ) :
    ordA 2 q = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) / Nat.gcd 3 (q - 1) := by
  unfold ordA
  rw [show Finset.Icc 2 (2 + 1) = {2, 3} by decide, Finset.prod_pair (by norm_num)]

theorem srcProfile_ordA_two {n : ℕ} (hn : 1 ≤ n) : SrcProfile (ordA 2 (2 ^ n)) := by
  by_cases h1 : n = 1
  · subst h1
    right; left
    decide
  have hn2 : 2 ≤ n := by omega
  have hq4 := four_le_two_pow hn2
  rw [ordA_two_eq]
  have hX : Odd (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) :=
    Odd.mul (odd_two_pow_pow_sub_one' (by omega) (by omega))
      (odd_two_pow_pow_sub_one' (by omega) (by omega))
  have hd : Nat.gcd 3 (2 ^ n - 1) ∣ ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1) := by
    refine (Nat.gcd_dvd_right 3 (2 ^ n - 1)).trans (dvd_mul_of_dvd_left ?_ _)
    simpa using Nat.sub_dvd_pow_sub_pow (2 ^ n) 1 2
  have hr : Odd (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1) / Nat.gcd 3 (2 ^ n - 1)) :=
    Odd.of_dvd_nat hX (Nat.div_dvd_of_dvd hd)
  rw [Nat.mul_div_assoc _ hd]
  have hlt : 4 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1) / Nat.gcd 3 (2 ^ n - 1)) <
      4 ^ (n * 3) := by
    rw [four_pow_eq]
    refine lt_of_le_of_lt (Nat.mul_le_mul_left 4 (Nat.div_le_self _ _)) ?_
    refine four_mul_lt_pow (i := 2) (j := 3) hq4 ?_ ?_ (by norm_num)
    · have : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ (by positivity)
      omega
    · have : 1 ≤ (2 ^ n) ^ 3 := Nat.one_le_pow _ _ (by positivity)
      omega
  have h := srcProfile_of_odd hr hlt
  rw [pow_mul] at h
  exact h

theorem ordTwistedA_two_eq' (q : ℕ) (hq : 1 ≤ q) :
    ordTwistedA 2 q = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) / Nat.gcd 3 (q + 1) := by
  have h1 : ((q : ℤ) ^ 2 - (-1) ^ 2).toNat = q ^ 2 - 1 := by
    rw [show ((q : ℤ) ^ 2 - (-1) ^ 2) = ((q ^ 2 - 1 : ℕ) : ℤ) by
      push_cast [Nat.cast_sub (Nat.one_le_pow _ _ hq)]; ring]
    exact Int.toNat_natCast _
  have h2 : ((q : ℤ) ^ 3 - (-1) ^ 3).toNat = q ^ 3 + 1 := by
    rw [show ((q : ℤ) ^ 3 - (-1) ^ 3) = ((q ^ 3 + 1 : ℕ) : ℤ) by push_cast; ring]
    exact Int.toNat_natCast _
  unfold ordTwistedA
  rw [show Finset.Icc 2 (2 + 1) = {2, 3} by decide, Finset.prod_pair (by norm_num), h1, h2]

theorem mul_lt_q5 {q a : ℕ} (hq : 4 ≤ q) (ha : a + 1 = q ^ 2) : a * (q ^ 3 + 1) < q ^ 5 := by
  have h5 : q ^ 5 = q ^ 2 * q ^ 3 := by ring
  have h23 : q ^ 2 ≤ q ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  rw [h5, ← ha]
  nlinarith

theorem srcProfile_ordTwistedA_two {n : ℕ} (hn : 2 ≤ n) :
    SrcProfile (ordTwistedA 2 (2 ^ n)) := by
  have hq4 := four_le_two_pow hn
  rw [ordTwistedA_two_eq' _ (by omega)]
  have hX : Odd (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1)) :=
    Odd.mul (odd_two_pow_pow_sub_one' (by omega) (by omega))
      (odd_two_pow_pow_add_one' (by omega) (by omega))
  have hd : Nat.gcd 3 (2 ^ n + 1) ∣ ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1) := by
    refine (Nat.gcd_dvd_right 3 (2 ^ n + 1)).trans (dvd_mul_of_dvd_left ?_ _)
    have h3 : 2 ^ n + 1 ∣ (2 ^ n) ^ 2 - 1 := ⟨2 ^ n - 1, by
      have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      zify [h1, Nat.one_le_pow 2 (2 ^ n) (by omega)]
      ring⟩
    exact h3
  have hr : Odd (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1) / Nat.gcd 3 (2 ^ n + 1)) :=
    Odd.of_dvd_nat hX (Nat.div_dvd_of_dvd hd)
  rw [Nat.mul_div_assoc _ hd]
  have hlt : 4 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1) / Nat.gcd 3 (2 ^ n + 1)) <
      4 ^ (n * 3) := by
    rw [four_pow_eq]
    refine lt_of_le_of_lt (Nat.mul_le_mul_left 4 (Nat.div_le_self _ _)) ?_
    have ha : ((2 ^ n) ^ 2 - 1) + 1 = (2 ^ n) ^ 2 :=
      Nat.sub_add_cancel (Nat.one_le_pow _ _ (by positivity))
    have h5 := mul_lt_q5 hq4 ha
    have h6 : 4 * (2 ^ n) ^ 5 ≤ (2 ^ n) ^ (2 * 3) := by
      have := four_mul_pow_le (k := 5) hq4
      simpa using this
    omega
  have h := srcProfile_of_odd hr hlt
  rw [pow_mul] at h
  exact h

theorem ordSuzuki_eq (q : ℕ) : ordSuzuki q = q ^ 2 * ((q ^ 2 + 1) * (q - 1)) := by
  unfold ordSuzuki
  ring

theorem mul_lt_q3 {q : ℕ} (hq : 1 ≤ q) : (q ^ 2 + 1) * (q - 1) < q ^ 3 := by
  obtain ⟨a, rfl⟩ : ∃ a, q = a + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  nlinarith [Nat.zero_le a]

theorem srcProfile_ordSuzuki {n : ℕ} (hn : 2 ≤ n) : SrcProfile (ordSuzuki (2 ^ n)) := by
  have hq4 := four_le_two_pow hn
  rw [ordSuzuki_eq]
  have hodd1 : Odd (2 ^ n - 1) := by
    have h := odd_two_pow_pow_sub_one' (n := n) (k := 1) (by omega) le_rfl
    simpa using h
  have hr : Odd (((2 ^ n) ^ 2 + 1) * (2 ^ n - 1)) :=
    Odd.mul (odd_two_pow_pow_add_one' (by omega) (by omega)) hodd1
  have hlt : 4 * (((2 ^ n) ^ 2 + 1) * (2 ^ n - 1)) < 4 ^ (n * 2) := by
    rw [four_pow_eq]
    have h3 := mul_lt_q3 (show 1 ≤ 2 ^ n by omega)
    have h4 : 4 * (2 ^ n) ^ 3 ≤ (2 ^ n) ^ (2 * 2) := by
      have := four_mul_pow_le (k := 3) hq4
      simpa using this
    omega
  have h := srcProfile_of_odd hr hlt
  rw [pow_mul] at h
  exact h

theorem srcProfile_6048 : SrcProfile 6048 :=
  srcProfile_of_odd (N := 5) (r := 189) (by decide) (by norm_num)

theorem coprime_two_pow_of_odd {N x : ℕ} (hx : x % 2 = 1) : Nat.Coprime (2 ^ N) x :=
  Nat.Coprime.pow_left N (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hx))

theorem four_pow_eq_sq (N : ℕ) : (4 : ℕ) ^ N = (2 ^ N) ^ 2 := by
  rw [← pow_mul, mul_comm, pow_mul]
  norm_num

theorem profile_contra {c B : ℕ} (hprof : SrcProfile c)
    (hdiv : ∀ N : ℕ, 2 ^ N ∣ c → 2 ^ N ≤ B) (hbig : B ^ 3 ≤ c) (h360 : 360 < c) : False := by
  rcases hprof with ⟨m, hm, hcm⟩ | h168 | h360' | ⟨N, r, hr, hcN, hlt⟩
  · have hQ : 2 ^ m ∣ c := by
      rw [hcm]
      exact Dvd.intro _ rfl
    have h1 := hdiv m hQ
    have h2 := ordL2_add_pow m
    have h3 : (2 ^ m) ^ 3 ≤ B ^ 3 := Nat.pow_le_pow_left h1 3
    have h4 : 0 < 2 ^ m := by positivity
    omega
  · omega
  · omega
  · have hQ : 2 ^ N ∣ c := by
      rw [hcN]
      exact Dvd.intro _ rfl
    have h1 := hdiv N hQ
    have h3 : (2 ^ N) ^ 3 ≤ B ^ 3 := Nat.pow_le_pow_left h1 3
    rw [four_pow_eq_sq] at hlt
    have h4 : 0 < 2 ^ N := by positivity
    have h5 : 2 ^ N * (4 * r) < 2 ^ N * (2 ^ N) ^ 2 := Nat.mul_lt_mul_of_pos_left hlt h4
    have h6 : 4 * c = 2 ^ N * (4 * r) := by rw [hcN]; ring
    have h7 : 2 ^ N * (2 ^ N) ^ 2 = (2 ^ N) ^ 3 := by ring
    omega

theorem ordL2_ne (m : ℕ) (hm : 2 ≤ m) : ordL2 m ≠ 168 ∧ ordL2 m ≠ 360 := by
  by_cases h2 : m = 2
  · subst h2
    unfold ordL2
    norm_num
  · have h3 : 3 ≤ m := by omega
    have hQ : 8 ≤ 2 ^ m :=
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h3
    have h64 : 64 ≤ (2 ^ m) ^ 2 := by nlinarith
    have : 8 * 63 ≤ ordL2 m := by
      unfold ordL2
      exact Nat.mul_le_mul hQ (by omega)
    omega

end Profile

section Odd

theorem two_pow_dvd_aux {N a : ℕ} (h : 2 ^ N ∣ 2 * a * (a + 1) * (2 * a + 1)) :
    2 ^ N ∣ 2 * (a + 1) ∨ 2 ^ N ∣ 2 * a := by
  have h1 : 2 ^ N ∣ 2 * a * (a + 1) :=
    (coprime_two_pow_of_odd (N := N) (x := 2 * a + 1) (by omega)).dvd_of_dvd_mul_right h
  rcases Nat.even_or_odd a with ha | ha
  · right
    have hco : Nat.Coprime (2 ^ N) (a + 1) :=
      coprime_two_pow_of_odd (by obtain ⟨k, hk⟩ := ha; omega)
    exact hco.dvd_of_dvd_mul_right h1
  · left
    have hco : Nat.Coprime (2 ^ N) a := coprime_two_pow_of_odd (by obtain ⟨k, hk⟩ := ha; omega)
    have h2 : 2 ^ N ∣ a * (2 * (a + 1)) := by
      rwa [show 2 * a * (a + 1) = a * (2 * (a + 1)) by ring] at h1
    exact hco.dvd_of_dvd_mul_left h2

theorem cubic_mono {a b : ℕ} (hab : b ≤ a) :
    2 * b * (b + 1) * (2 * b + 1) ≤ 2 * a * (a + 1) * (2 * a + 1) := by
  gcongr

theorem psl_two_core {a c : ℕ} (ha : 2 ≤ a) (hc : c = 2 * a * (a + 1) * (2 * a + 1))
    (h8 : (2 * a + 1) % 8 = 1 ∨ (2 * a + 1) % 8 = 7) (hprof : SrcProfile c) : a = 3 ∨ a = 4 := by
  rcases hprof with ⟨m, hm, hcm⟩ | h168 | h360 | ⟨N, r, hr, hcN, hlt⟩
  · exfalso
    have hQ4 : 4 ≤ 2 ^ m := four_le_two_pow hm
    have hdiv : 2 ^ m ∣ 2 * a * (a + 1) * (2 * a + 1) := by
      rw [← hc, hcm]
      exact Dvd.intro _ rfl
    have heq : 2 * a * (a + 1) * (2 * a + 1) + 2 ^ m = (2 ^ m) ^ 3 := by
      rw [← hc, hcm]
      exact ordL2_add_pow m
    have hd2 := two_pow_dvd_aux hdiv
    generalize 2 ^ m = Q at hQ4 hd2 heq
    have hQpos : 0 < Q := by omega
    rcases hd2 with ⟨t, ht⟩ | ⟨t, ht⟩
    · have hE : 2 * a * (a + 1) * (2 * a + 1) = Q * (a * t * (2 * a + 1)) := by
        calc 2 * a * (a + 1) * (2 * a + 1) = a * (2 * (a + 1)) * (2 * a + 1) := by ring
          _ = a * (Q * t) * (2 * a + 1) := by rw [ht]
          _ = Q * (a * t * (2 * a + 1)) := by ring
      have h2 : a * t * (2 * a + 1) + 1 = Q ^ 2 := by
        apply Nat.eq_of_mul_eq_mul_left hQpos
        rw [hE] at heq
        nlinarith
      by_cases ht0 : t = 0
      · subst ht0
        omega
      by_cases ht1 : t = 1
      · subst ht1
        have : Q = 2 * (a + 1) := by omega
        subst this
        nlinarith
      by_cases ht2 : t = 2
      · subst ht2
        have : Q = a + 1 := by omega
        subst this
        nlinarith
      have ht3 : 3 ≤ t := by omega
      have h3 : 3 * Q ≤ 2 * (a + 1) := by
        rw [ht]
        nlinarith
      have h4 : (3 * Q) ^ 2 ≤ (2 * (a + 1)) ^ 2 := Nat.pow_le_pow_left h3 2
      have h5 : 3 * a * (2 * a + 1) ≤ a * t * (2 * a + 1) := by nlinarith
      nlinarith
    · have hE : 2 * a * (a + 1) * (2 * a + 1) = Q * (t * (a + 1) * (2 * a + 1)) := by
        calc 2 * a * (a + 1) * (2 * a + 1) = (2 * a) * (a + 1) * (2 * a + 1) := by ring
          _ = (Q * t) * (a + 1) * (2 * a + 1) := by rw [ht]
          _ = Q * (t * (a + 1) * (2 * a + 1)) := by ring
      have h2 : t * (a + 1) * (2 * a + 1) + 1 = Q ^ 2 := by
        apply Nat.eq_of_mul_eq_mul_left hQpos
        rw [hE] at heq
        nlinarith
      by_cases ht0 : t = 0
      · subst ht0
        omega
      by_cases ht1 : t = 1
      · subst ht1
        have hQ : Q = 2 * a := by omega
        subst hQ
        have ha2 : a ≤ 2 := by nlinarith
        have : a = 2 := by omega
        subst this
        omega
      by_cases ht2 : t = 2
      · subst ht2
        have : Q = a := by omega
        subst this
        nlinarith
      have ht3 : 3 ≤ t := by omega
      have h3 : 3 * Q ≤ 2 * a := by
        rw [ht]
        nlinarith
      have h4 : (3 * Q) ^ 2 ≤ (2 * a) ^ 2 := Nat.pow_le_pow_left h3 2
      have h5 : 3 * (a + 1) * (2 * a + 1) ≤ t * (a + 1) * (2 * a + 1) := by nlinarith
      nlinarith
  · left
    have h4 : a ≤ 3 := by
      by_contra hcon
      push Not at hcon
      have := cubic_mono (show 4 ≤ a by omega)
      omega
    interval_cases a <;> omega
  · right
    have h4 : a ≤ 4 := by
      by_contra hcon
      push Not at hcon
      have := cubic_mono (show 5 ≤ a by omega)
      omega
    interval_cases a <;> omega
  · exfalso
    have hdiv : 2 ^ N ∣ 2 * a * (a + 1) * (2 * a + 1) := by
      rw [← hc, hcN]
      exact Dvd.intro _ rfl
    have hQle : 2 ^ N ≤ 2 * (a + 1) := by
      rcases two_pow_dvd_aux hdiv with h | h
      · exact Nat.le_of_dvd (by omega) h
      · exact (Nat.le_of_dvd (by omega) h).trans (by omega)
    have hQr : 2 ^ N * r = 2 * a * (a + 1) * (2 * a + 1) := by rw [← hc, hcN]
    rw [four_pow_eq_sq] at hlt
    generalize 2 ^ N = Q at hQle hQr hlt
    have h1 : 2 * (a + 1) * (a * (2 * a + 1)) ≤ 2 * (a + 1) * r := by
      calc 2 * (a + 1) * (a * (2 * a + 1)) = 2 * a * (a + 1) * (2 * a + 1) := by ring
        _ = Q * r := hQr.symm
        _ ≤ 2 * (a + 1) * r := Nat.mul_le_mul_right r hQle
    have h2 : a * (2 * a + 1) ≤ r := Nat.le_of_mul_le_mul_left h1 (by omega)
    have h3 : Q ^ 2 ≤ (2 * (a + 1)) ^ 2 := Nat.pow_le_pow_left hQle 2
    nlinarith

theorem card_of_isPSL {n p e : ℕ} {Y : Type} [Group Y] (h : IsPSL n p e Y) :
    Nat.card Y = ordA (n - 1) (p ^ e) := by
  obtain ⟨⟨-, -, hn, -, -⟩, K, _, _, hK, ⟨eq⟩⟩ := h
  rw [Nat.card_congr eq.toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by omega), hK, ordA,
    Nat.sub_add_cancel (by omega : 1 ≤ n), mul_comm (n - 1) n]

theorem ordA_one_eq (q : ℕ) : ordA 1 q = q * (q ^ 2 - 1) / Nat.gcd 2 (q - 1) := by
  unfold ordA
  simp

theorem exists_odd_decomp {p e : ℕ} (hp : p.Prime) (hp3 : 3 < p) (he : 1 ≤ e) :
    ∃ a : ℕ, 2 ≤ a ∧ p ^ e = 2 * a + 1 := by
  have hp2 : p ≠ 2 := by omega
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hpe : Odd (p ^ e) := hodd.pow
  obtain ⟨a, ha⟩ := hpe
  refine ⟨a, ?_, ha⟩
  have h1 : p ≤ p ^ e := Nat.le_self_pow (by omega) p
  have h5 : 5 ≤ p := by
    obtain ⟨k, hk⟩ := hodd
    omega
  omega

theorem t1_proof (c p e : ℕ) (hprof : SrcProfile c) (hT : IsT1 p e) (Y : Type) [Group Y]
    (hY : IsPSL 2 p e Y) (hc : Nat.card Y = c) : c = 168 ∧ p = 7 ∧ e = 1 := by
  obtain ⟨hp, hp3, he, h8⟩ := hT
  have he1 : 1 ≤ e := by omega
  obtain ⟨a, ha, hqa⟩ := exists_odd_decomp hp hp3 he1
  have hcard := card_of_isPSL hY
  rw [hc, hqa, show 2 - 1 = 1 by norm_num, ordA_one_eq] at hcard
  have hsq : (2 * a + 1) ^ 2 - 1 = 4 * (a * (a + 1)) := by
    have : (2 * a + 1) ^ 2 = 4 * (a * (a + 1)) + 1 := by ring
    omega
  have hg : Nat.gcd 2 (2 * a + 1 - 1) = 2 := by
    rw [show 2 * a + 1 - 1 = 2 * a by omega]
    exact Nat.gcd_eq_left (dvd_mul_right 2 a)
  rw [hsq, hg] at hcard
  have hc' : c = 2 * a * (a + 1) * (2 * a + 1) := by
    rw [hcard]
    have : (2 * a + 1) * (4 * (a * (a + 1))) = 2 * (2 * a * (a + 1) * (2 * a + 1)) := by ring
    rw [this]
    exact Nat.mul_div_cancel_left _ (by norm_num)
  rw [hqa] at h8
  rcases psl_two_core ha hc' h8 hprof with h3 | h4
  · subst h3
    have hc7 : c = 168 := by rw [hc']
    have hq7 : p ^ e = 7 := by omega
    rcases he with rfl | rfl
    · exact ⟨hc7, by simpa using hq7, rfl⟩
    · exfalso
      have hp4 : p ≠ 4 := by
        rintro rfl
        exact absurd hp (by norm_num)
      have : 5 * 5 ≤ p * p := Nat.mul_le_mul (by omega) (by omega)
      nlinarith
  · exfalso
    subst h4
    have hq9 : p ^ e = 9 := by omega
    rcases he with rfl | rfl
    · rw [pow_one] at hq9
      subst hq9
      exact absurd hp (by norm_num)
    · have : p * p = 9 := by nlinarith
      have : p = 3 := by nlinarith
      omega

theorem two_pow_dvd_of_odd_mul {N x y : ℕ} (hx : x % 2 = 1) (h : 2 ^ N ∣ x * y) : 2 ^ N ∣ y :=
  (coprime_two_pow_of_odd hx).dvd_of_dvd_mul_left h

theorem two_pow_dvd_of_mul_odd {N x y : ℕ} (hx : x % 2 = 1) (h : 2 ^ N ∣ y * x) : 2 ^ N ∣ y :=
  (coprime_two_pow_of_odd hx).dvd_of_dvd_mul_right h

theorem odd_pow_mod {x n : ℕ} (hx : x % 2 = 1) : x ^ n % 2 = 1 := by
  rw [Nat.pow_mod, hx]
  simp

theorem t2_core {k c d : ℕ} (hk : 1 ≤ k) (hd : d ≤ 3)
    (hcd : c * d = (4 * k + 1) ^ 3 * (16 * k * ((2 * k + 1) ^ 2 * (16 * k ^ 2 + 4 * k + 1))))
    (hprof : SrcProfile c) : False := by
  have hdiv : ∀ N : ℕ, 2 ^ N ∣ c → 2 ^ N ≤ 16 * k := by
    intro N hN
    have h1 : 2 ^ N ∣ c * d := dvd_mul_of_dvd_left hN d
    rw [hcd] at h1
    have h2 := two_pow_dvd_of_odd_mul (odd_pow_mod (x := 4 * k + 1) (n := 3) (by omega)) h1
    have h3 := two_pow_dvd_of_mul_odd (x := (2 * k + 1) ^ 2 * (16 * k ^ 2 + 4 * k + 1))
      (by
        rw [Nat.mul_mod, odd_pow_mod (x := 2 * k + 1) (n := 2) (by omega)]
        have : (16 * k ^ 2 + 4 * k + 1) % 2 = 1 := by omega
        rw [this])
      h2
    exact Nat.le_of_dvd (by omega) h3
  have hbig : 3 * (16 * k) ^ 3 ≤ c * d := by
    rw [hcd]
    have h1 : (4 * k) ^ 3 ≤ (4 * k + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have h2 : (2 * k) ^ 2 ≤ (2 * k + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h3 : 16 * k ^ 2 ≤ 16 * k ^ 2 + 4 * k + 1 := by omega
    have h4 : (4 * k) ^ 3 * (16 * k * ((2 * k) ^ 2 * (16 * k ^ 2))) ≤
        (4 * k + 1) ^ 3 * (16 * k * ((2 * k + 1) ^ 2 * (16 * k ^ 2 + 4 * k + 1))) :=
      Nat.mul_le_mul h1 (Nat.mul_le_mul_left _ (Nat.mul_le_mul h2 h3))
    have e1 : (4 * k) ^ 3 * (16 * k * ((2 * k) ^ 2 * (16 * k ^ 2))) = 65536 * k ^ 8 := by ring
    have e2 : 3 * (16 * k) ^ 3 = 12288 * k ^ 3 := by ring
    have h5 : k ^ 3 ≤ k ^ 8 := Nat.pow_le_pow_right hk (by norm_num)
    rw [e2]
    rw [e1] at h4
    omega
  have hbig' : (16 * k) ^ 3 ≤ c := by
    have h1 : c * d ≤ c * 3 := Nat.mul_le_mul_left c hd
    have h2 : 3 * (16 * k) ^ 3 ≤ 3 * c := by omega
    exact Nat.le_of_mul_le_mul_left h2 (by norm_num)
  have h4096 : 4096 ≤ (16 * k) ^ 3 := by
    have : 16 ≤ 16 * k := by omega
    calc 4096 = 16 ^ 3 := by norm_num
      _ ≤ (16 * k) ^ 3 := Nat.pow_le_pow_left this 3
  exact profile_contra hprof hdiv hbig' (by omega)

theorem t3_core {k c d : ℕ} (hd : d ≤ 3) (hk0 : k = 0 → d = 1)
    (hcd : c * d =
      (4 * k + 3) ^ 3 * (16 * (k + 1) * ((2 * k + 1) ^ 2 * (16 * k ^ 2 + 28 * k + 13))))
    (hprof : SrcProfile c) : False := by
  have hdiv : ∀ N : ℕ, 2 ^ N ∣ c → 2 ^ N ≤ 16 * (k + 1) := by
    intro N hN
    have h1 : 2 ^ N ∣ c * d := dvd_mul_of_dvd_left hN d
    rw [hcd] at h1
    have h2 := two_pow_dvd_of_odd_mul (odd_pow_mod (x := 4 * k + 3) (n := 3) (by omega)) h1
    have h3 := two_pow_dvd_of_mul_odd (x := (2 * k + 1) ^ 2 * (16 * k ^ 2 + 28 * k + 13))
      (by
        rw [Nat.mul_mod, odd_pow_mod (x := 2 * k + 1) (n := 2) (by omega)]
        have : (16 * k ^ 2 + 28 * k + 13) % 2 = 1 := by omega
        rw [this])
      h2
    exact Nat.le_of_dvd (by omega) h3
  have hbig' : (16 * (k + 1)) ^ 3 ≤ c := by
    by_cases hk : k = 0
    · subst hk
      have hd1 := hk0 rfl
      subst hd1
      norm_num at hcd ⊢
      omega
    · have hk1 : 1 ≤ k := by omega
      have hbig : 3 * (16 * (k + 1)) ^ 3 ≤ c * d := by
        rw [hcd]
        have h1 : (3 * (k + 1)) ^ 3 ≤ (4 * k + 3) ^ 3 := Nat.pow_le_pow_left (by omega) 3
        have h2 : (k + 1) ^ 2 ≤ (2 * k + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
        have h3 : 13 ≤ 16 * k ^ 2 + 28 * k + 13 := by omega
        have h4 : (3 * (k + 1)) ^ 3 * (16 * (k + 1) * ((k + 1) ^ 2 * 13)) ≤
            (4 * k + 3) ^ 3 * (16 * (k + 1) * ((2 * k + 1) ^ 2 * (16 * k ^ 2 + 28 * k + 13))) :=
          Nat.mul_le_mul h1 (Nat.mul_le_mul_left _ (Nat.mul_le_mul h2 h3))
        have e1 : (3 * (k + 1)) ^ 3 * (16 * (k + 1) * ((k + 1) ^ 2 * 13)) = 5616 * (k + 1) ^ 6 := by
          ring
        have e2 : 3 * (16 * (k + 1)) ^ 3 = 12288 * (k + 1) ^ 3 := by ring
        have h8 : 8 ≤ (k + 1) ^ 3 :=
          calc 8 = 2 ^ 3 := by norm_num
            _ ≤ (k + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
        have h5 : 8 * (k + 1) ^ 3 ≤ (k + 1) ^ 6 := by
          have e : (k + 1) ^ 6 = (k + 1) ^ 3 * (k + 1) ^ 3 := by ring
          rw [e]
          exact Nat.mul_le_mul_right _ h8
        rw [e2]
        rw [e1] at h4
        omega
      have h1 : c * d ≤ c * 3 := Nat.mul_le_mul_left c hd
      have h2 : 3 * (16 * (k + 1)) ^ 3 ≤ 3 * c := by omega
      exact Nat.le_of_mul_le_mul_left h2 (by norm_num)
  have h4096 : 4096 ≤ (16 * (k + 1)) ^ 3 := by
    have : 16 ≤ 16 * (k + 1) := by omega
    calc 4096 = 16 ^ 3 := by norm_num
      _ ≤ (16 * (k + 1)) ^ 3 := Nat.pow_le_pow_left this 3
  exact profile_contra hprof hdiv hbig' (by omega)

theorem succ_dvd_sq_sub_one (q : ℕ) (hq : 1 ≤ q) : q + 1 ∣ q ^ 2 - 1 :=
  ⟨q - 1, by
    have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
    zify [h1, hq]
    ring⟩

theorem card_of_isPSU_three {p : ℕ} (hp : p.Prime) {Y : Type} [Group Y] (h : IsPSU 3 p 1 Y) :
    Nat.card Y = ordTwistedA 2 p := by
  obtain ⟨-, K, _, _, hK, ⟨eq⟩⟩ := h
  rw [Nat.card_congr eq.toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU hp (le_refl 1) hK (by norm_num)]
  simp only [pow_one]
  rfl

theorem t2_proof (c p : ℕ) (hprof : SrcProfile c) (hp : p.Prime) (h4 : p % 4 = 1) (Y : Type)
    [Group Y] (hY : IsPSU 3 p 1 Y) : Nat.card Y ≠ c := by
  intro hc
  have hcard := card_of_isPSU_three hp hY
  rw [hc, ordTwistedA_two_eq' p hp.one_lt.le] at hcard
  obtain ⟨k, hk⟩ : ∃ k, p = 4 * k + 1 := ⟨p / 4, by omega⟩
  have hk1 : 1 ≤ k := by
    by_contra h0
    have : k = 0 := by omega
    subst this
    exact absurd hk (by have := hp.two_le; omega)
  subst hk
  have hd3 : Nat.gcd 3 (4 * k + 1 + 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
  have hdvd : Nat.gcd 3 (4 * k + 1 + 1) ∣
      (4 * k + 1) ^ 3 * (((4 * k + 1) ^ 2 - 1) * ((4 * k + 1) ^ 3 + 1)) :=
    dvd_mul_of_dvd_right ((Nat.gcd_dvd_right 3 _).trans
      ((succ_dvd_sq_sub_one _ (by omega)).trans (Dvd.intro _ rfl))) _
  have hcd : c * Nat.gcd 3 (4 * k + 1 + 1) =
      (4 * k + 1) ^ 3 * (((4 * k + 1) ^ 2 - 1) * ((4 * k + 1) ^ 3 + 1)) := by
    rw [hcard]
    exact Nat.div_mul_cancel hdvd
  have e1 : (4 * k + 1) ^ 2 - 1 = 8 * k * (2 * k + 1) := Nat.sub_eq_of_eq_add (by ring)
  have e2 : (4 * k + 1) ^ 3 + 1 = 2 * (2 * k + 1) * (16 * k ^ 2 + 4 * k + 1) := by ring
  rw [e1, e2] at hcd
  have hcd' : c * Nat.gcd 3 (4 * k + 1 + 1) =
      (4 * k + 1) ^ 3 * (16 * k * ((2 * k + 1) ^ 2 * (16 * k ^ 2 + 4 * k + 1))) := by
    rw [hcd]
    ring
  exact t2_core hk1 hd3 hcd' hprof

theorem card_of_isPSL_three {p : ℕ} {Y : Type} [Group Y] (h : IsPSL 3 p 1 Y) :
    Nat.card Y = ordA 2 p := by
  have := card_of_isPSL h
  simpa using this

theorem t3_proof (c p : ℕ) (hprof : SrcProfile c) (hp : p.Prime) (h4 : p % 4 = 3) (Y : Type)
    [Group Y] (hY : IsPSL 3 p 1 Y) : Nat.card Y ≠ c := by
  intro hc
  have hcard := card_of_isPSL_three hY
  rw [hc, ordA_two_eq] at hcard
  obtain ⟨k, hk⟩ : ∃ k, p = 4 * k + 3 := ⟨p / 4, by omega⟩
  subst hk
  have hd3 : Nat.gcd 3 (4 * k + 3 - 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
  have hdvd : Nat.gcd 3 (4 * k + 3 - 1) ∣
      (4 * k + 3) ^ 3 * (((4 * k + 3) ^ 2 - 1) * ((4 * k + 3) ^ 3 - 1)) := by
    refine dvd_mul_of_dvd_right (dvd_mul_of_dvd_left ((Nat.gcd_dvd_right 3 _).trans ?_) _) _
    simpa using Nat.sub_dvd_pow_sub_pow (4 * k + 3) 1 2
  have hcd : c * Nat.gcd 3 (4 * k + 3 - 1) =
      (4 * k + 3) ^ 3 * (((4 * k + 3) ^ 2 - 1) * ((4 * k + 3) ^ 3 - 1)) := by
    rw [hcard]
    exact Nat.div_mul_cancel hdvd
  have e1 : (4 * k + 3) ^ 2 - 1 = 8 * (2 * k + 1) * (k + 1) := Nat.sub_eq_of_eq_add (by ring)
  have e2 : (4 * k + 3) ^ 3 - 1 = 2 * (2 * k + 1) * (16 * k ^ 2 + 28 * k + 13) :=
    Nat.sub_eq_of_eq_add (by ring)
  rw [e1, e2] at hcd
  have hcd' : c * Nat.gcd 3 (4 * k + 3 - 1) =
      (4 * k + 3) ^ 3 * (16 * (k + 1) * ((2 * k + 1) ^ 2 * (16 * k ^ 2 + 28 * k + 13))) := by
    rw [hcd]
    ring
  refine t3_core hd3 (fun hk0 => ?_) hcd' hprof
  subst hk0
  decide

end Odd

theorem arithAll : ArithAll where
  t0 := ordL2_ne
  t1 := fun c p e hprof hT Y _ hY hc => t1_proof c p e hprof hT Y hY hc
  t2 := fun c p hprof hp h4 Y _ hY => t2_proof c p hprof hp h4 Y hY
  t3 := fun c p hprof hp h4 Y _ hY => t3_proof c p hprof hp h4 Y hY

end CFSG.Quasithin.GoldS146R
