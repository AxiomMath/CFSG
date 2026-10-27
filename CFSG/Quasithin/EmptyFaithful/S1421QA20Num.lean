module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Quasithin.S1421QA20

theorem pow_two_eq_of_mul_odd {a b x y : ℕ} (hx : Odd x) (hy : Odd y)
    (h : 2 ^ a * x = 2 ^ b * y) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exfalso
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt hab
    have h2 : x = 2 ^ (c + 1) * y := by
      apply Nat.eq_of_mul_eq_mul_left (show 0 < 2 ^ a by positivity)
      rw [h]; ring
    have h3 : x = 2 * (2 ^ c * y) := by rw [h2]; ring
    have := Nat.odd_iff.mp hx
    omega
  · exact hab
  · exfalso
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt hab
    have h2 : y = 2 ^ (c + 1) * x := by
      apply Nat.eq_of_mul_eq_mul_left (show 0 < 2 ^ b by positivity)
      rw [← h]; ring
    have h3 : y = 2 * (2 ^ c * x) := by rw [h2]; ring
    have := Nat.odd_iff.mp hy
    omega

theorem two_adic_aux {t j A W : ℕ} (hA : Odd A) (ht : 1 ≤ t)
    (hW : W = t ^ 2 * (t + 1) ∨ W = t * (t + 1) ^ 2) (h : 2 ^ (j + 3) ∣ A * (8 * W)) :
    2 ^ (j + 2) ≤ (2 * t + 2) ^ 2 := by
  have hcop : Nat.Coprime (2 ^ (j + 3)) A :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hA)
  have h1 : 2 ^ (j + 3) ∣ 8 * W := hcop.dvd_of_dvd_mul_left h
  have h2 : 2 ^ j ∣ W := by
    have : 8 * 2 ^ j ∣ 8 * W := by
      have e : 2 ^ (j + 3) = 8 * 2 ^ j := by rw [pow_add]; ring
      rwa [e] at h1
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
  have hjpos : 0 < 2 ^ j := by positivity
  have e4 : 2 ^ (j + 2) = 4 * 2 ^ j := by rw [pow_add]; ring
  rcases Nat.even_or_odd t with he | ho
  · have hodd : Odd (t + 1) := he.add_one
    have hc1 : Nat.Coprime (2 ^ j) (t + 1) :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
    have hc2 : Nat.Coprime (2 ^ j) ((t + 1) ^ 2) := Nat.Coprime.pow_right _ hc1
    rcases hW with rfl | rfl
    · have h3 : 2 ^ j ∣ t ^ 2 := hc1.dvd_of_dvd_mul_right h2
      have h4 : 2 ^ j ≤ t ^ 2 := Nat.le_of_dvd (by positivity) h3
      rw [e4]
      nlinarith
    · have h3 : 2 ^ j ∣ t := hc2.dvd_of_dvd_mul_right h2
      have h4 : 2 ^ j ≤ t := Nat.le_of_dvd (by omega) h3
      rw [e4]
      nlinarith
  · have hc1 : Nat.Coprime (2 ^ j) t := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr ho)
    have hc2 : Nat.Coprime (2 ^ j) (t ^ 2) := Nat.Coprime.pow_right _ hc1
    rcases hW with rfl | rfl
    · have h3 : 2 ^ j ∣ t + 1 := hc2.dvd_of_dvd_mul_left h2
      have h4 : 2 ^ j ≤ t + 1 := Nat.le_of_dvd (by omega) h3
      rw [e4]
      nlinarith
    · have h3 : 2 ^ j ∣ (t + 1) ^ 2 := hc1.dvd_of_dvd_mul_left h2
      have h4 : 2 ^ j ≤ (t + 1) ^ 2 := Nat.le_of_dvd (by positivity) h3
      rw [e4]
      nlinarith

theorem odd_N_plus_bound {t j d T : ℕ} (ht : 1 ≤ t) (hT : 2 ^ (j + 3) ∣ T)
    (h : (2 * t + 1) ^ 3 * (((2 * t + 1) ^ 2 - 1) * ((2 * t + 1) ^ 3 - 1)) = d * T) :
    2 ^ (j + 2) ≤ (2 * t + 2) ^ 2 := by
  have e1 : (2 * t + 1) ^ 2 - 1 = 4 * t * (t + 1) := by
    apply Nat.sub_eq_of_eq_add; ring
  have e2 : (2 * t + 1) ^ 3 - 1 = 2 * t * ((2 * t + 1) ^ 2 + (2 * t + 1) + 1) := by
    apply Nat.sub_eq_of_eq_add; ring
  have hA : Odd ((2 * t + 1) ^ 3 * ((2 * t + 1) ^ 2 + (2 * t + 1) + 1)) := by
    refine Odd.mul (Odd.pow ⟨t, rfl⟩) ⟨2 * t ^ 2 + 3 * t + 1, by ring⟩
  have hN : 2 ^ (j + 3) ∣ ((2 * t + 1) ^ 3 * ((2 * t + 1) ^ 2 + (2 * t + 1) + 1)) *
      (8 * (t ^ 2 * (t + 1))) := by
    have : ((2 * t + 1) ^ 3 * ((2 * t + 1) ^ 2 + (2 * t + 1) + 1)) * (8 * (t ^ 2 * (t + 1))) =
        d * T := by
      rw [← h, e1, e2]; ring
    rw [this]
    exact Dvd.dvd.mul_left hT d
  exact two_adic_aux hA ht (Or.inl rfl) hN

theorem odd_N_minus_bound {t j d T : ℕ} (ht : 1 ≤ t) (hT : 2 ^ (j + 3) ∣ T)
    (h : (2 * t + 1) ^ 3 * (((2 * t + 1) ^ 2 - 1) * ((2 * t + 1) ^ 3 + 1)) = d * T) :
    2 ^ (j + 2) ≤ (2 * t + 2) ^ 2 := by
  have e1 : (2 * t + 1) ^ 2 - 1 = 4 * t * (t + 1) := by
    apply Nat.sub_eq_of_eq_add; ring
  have hA : Odd ((2 * t + 1) ^ 3 * (4 * t ^ 2 + 2 * t + 1)) := by
    refine Odd.mul (Odd.pow ⟨t, rfl⟩) ⟨2 * t ^ 2 + t, by ring⟩
  have hN : 2 ^ (j + 3) ∣ ((2 * t + 1) ^ 3 * (4 * t ^ 2 + 2 * t + 1)) *
      (8 * (t * (t + 1) ^ 2)) := by
    have : ((2 * t + 1) ^ 3 * (4 * t ^ 2 + 2 * t + 1)) * (8 * (t * (t + 1) ^ 2)) =
        d * T := by
      rw [← h, e1]; ring
    rw [this]
    exact Dvd.dvd.mul_left hT d
  exact two_adic_aux hA ht (Or.inr rfl) hN

theorem pow_eight_le_four_mul_N_plus {Q : ℕ} (hQ : 2 ≤ Q) :
    Q ^ 8 ≤ 4 * (Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 - 1))) := by
  have h1 : Q ^ 2 ≤ 2 * (Q ^ 2 - 1) := by
    have : 4 ≤ Q ^ 2 := by nlinarith
    omega
  have h2 : Q ^ 3 ≤ 2 * (Q ^ 3 - 1) := by
    have : 8 ≤ Q ^ 3 := by nlinarith [Nat.pow_le_pow_left hQ 3]
    omega
  have h3 : Q ^ 2 * Q ^ 3 ≤ (2 * (Q ^ 2 - 1)) * (2 * (Q ^ 3 - 1)) := Nat.mul_le_mul h1 h2
  calc Q ^ 8 = Q ^ 3 * (Q ^ 2 * Q ^ 3) := by ring
    _ ≤ Q ^ 3 * ((2 * (Q ^ 2 - 1)) * (2 * (Q ^ 3 - 1))) := Nat.mul_le_mul_left _ h3
    _ = 4 * (Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 - 1))) := by ring

theorem N_plus_le_N_minus (Q : ℕ) :
    Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 - 1)) ≤ Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 + 1)) :=
  Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))

theorem odd_final {T z m c Q d : ℕ} (hT : T = z ^ 3) (hz16 : 16 ≤ z) (hmc : m ≤ c * z ^ 4)
    (hc : 12 * c < z) (hQ : 3 ≤ Q) (hd3 : d ≤ 3) (hTQ : T ≤ 2 * (Q + 1) ^ 2)
    (hN : Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 - 1)) ≤ d * (T * m)) : False := by
  have hQ2 : (Q + 1) ^ 2 ≤ 2 * Q ^ 2 := by nlinarith
  have hT4 : T ≤ 4 * Q ^ 2 := by omega
  have h8 := pow_eight_le_four_mul_N_plus (Q := Q) (by omega)
  have hTpos : 0 < T := by rw [hT]; positivity
  have h1 : T ^ 4 ≤ 256 * Q ^ 8 :=
    calc T ^ 4 ≤ (4 * Q ^ 2) ^ 4 := Nat.pow_le_pow_left hT4 4
      _ = 256 * Q ^ 8 := by ring
  have h2 : d * (T * m) ≤ 3 * (T * m) := Nat.mul_le_mul_right _ hd3
  have h3 : T ^ 4 ≤ 3072 * (T * m) := by omega
  have h4 : T ^ 3 ≤ 3072 * m := by
    have : T * T ^ 3 ≤ T * (3072 * m) :=
      calc T * T ^ 3 = T ^ 4 := by ring
        _ ≤ 3072 * (T * m) := h3
        _ = T * (3072 * m) := by ring
    exact Nat.le_of_mul_le_mul_left this hTpos
  have h5 : z ^ 9 ≤ 3072 * (c * z ^ 4) :=
    calc z ^ 9 = T ^ 3 := by rw [hT]; ring
      _ ≤ 3072 * m := h4
      _ ≤ 3072 * (c * z ^ 4) := Nat.mul_le_mul_left _ hmc
  have hz4 : 0 < z ^ 4 := by positivity
  have h6 : z ^ 5 ≤ 3072 * c := by
    have : z ^ 4 * z ^ 5 ≤ z ^ 4 * (3072 * c) :=
      calc z ^ 4 * z ^ 5 = z ^ 9 := by ring
        _ ≤ 3072 * (c * z ^ 4) := h5
        _ = z ^ 4 * (3072 * c) := by ring
    exact Nat.le_of_mul_le_mul_left this hz4
  have h7 : 256 * z ≤ z ^ 5 := by
    have h16 : 16 ^ 4 ≤ z ^ 4 := Nat.pow_le_pow_left hz16 4
    have : z * 256 ≤ z * z ^ 4 := Nat.mul_le_mul_left _ (by omega)
    calc 256 * z = z * 256 := by ring
      _ ≤ z * z ^ 4 := this
      _ = z ^ 5 := by ring
  omega

theorem odd_cube_of_even {q : ℕ} (hq : 2 ≤ q) (hqe : Even q) :
    Odd (q ^ 3 - 1) ∧ Odd (q ^ 3 + 1) := by
  have h : Even (q ^ 3) := Nat.even_pow.mpr ⟨hqe, by norm_num⟩
  have h1 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
  obtain ⟨k, hk⟩ := h
  exact ⟨⟨k - 1, by omega⟩, ⟨k, by omega⟩⟩

theorem odd_sq_sub_one_of_even {q : ℕ} (hq : 2 ≤ q) (hqe : Even q) : Odd (q ^ 2 - 1) := by
  have h : Even (q ^ 2) := Nat.even_pow.mpr ⟨hqe, by norm_num⟩
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  obtain ⟨k, hk⟩ := h
  exact ⟨k - 1, by omega⟩

theorem size_even {z m c : ℕ} (hz16 : 16 ≤ z) (hmc : m ≤ c * z ^ 4) (hc : 12 * c < z) :
    3 * m < (z ^ 2 - 1) * (z ^ 3 - 1) := by
  have h1 : z ^ 2 ≤ 2 * (z ^ 2 - 1) := by
    have : 4 ≤ z ^ 2 := by nlinarith
    omega
  have h2 : z ^ 3 ≤ 2 * (z ^ 3 - 1) := by
    have : 8 ≤ z ^ 3 := by nlinarith [Nat.pow_le_pow_left hz16 3]
    omega
  have h3 : z ^ 2 * z ^ 3 ≤ (2 * (z ^ 2 - 1)) * (2 * (z ^ 3 - 1)) := Nat.mul_le_mul h1 h2
  have h4 : z ^ 5 ≤ 4 * ((z ^ 2 - 1) * (z ^ 3 - 1)) :=
    calc z ^ 5 = z ^ 2 * z ^ 3 := by ring
      _ ≤ (2 * (z ^ 2 - 1)) * (2 * (z ^ 3 - 1)) := h3
      _ = 4 * ((z ^ 2 - 1) * (z ^ 3 - 1)) := by ring
  have hz4 : 0 < z ^ 4 := by positivity
  have h5 : (12 * c) * z ^ 4 < z * z ^ 4 := Nat.mul_lt_mul_of_pos_right hc hz4
  have h6 : 12 * m ≤ 12 * (c * z ^ 4) := Nat.mul_le_mul_left _ hmc
  have h7 : z * z ^ 4 = z ^ 5 := by ring
  have h8 : (12 * c) * z ^ 4 = 12 * (c * z ^ 4) := by ring
  omega

theorem even_final {s z m c q d w : ℕ} (hz : 2 ^ s = z ^ 3) (hz16 : 16 ≤ z) (hm : Odd m)
    (hmc : m ≤ c * z ^ 4) (hc : 12 * c < z) (hd : Odd d) (hd3 : d ≤ 3) (hq : 2 ≤ q)
    (hqe : Even q) (hw : Odd w) (hwq : q ^ 3 - 1 ≤ w)
    (h : 2 ^ s * m * d = q ^ 3 * ((q ^ 2 - 1) * w)) : False := by
  have hsq := odd_sq_sub_one_of_even hq hqe
  obtain ⟨a, b, hb, hqab⟩ := Nat.exists_eq_two_pow_mul_odd (show q ≠ 0 by omega)
  have hb1 : 1 ≤ b := hb.pos
  have hodd : Odd (b ^ 3 * ((q ^ 2 - 1) * w)) := hb.pow.mul (hsq.mul hw)
  have h3a : 3 * a = s := by
    refine pow_two_eq_of_mul_odd hodd (hm.mul hd) ?_
    have e : q ^ 3 = 2 ^ (3 * a) * b ^ 3 := by rw [hqab]; ring
    calc 2 ^ (3 * a) * (b ^ 3 * ((q ^ 2 - 1) * w)) = q ^ 3 * ((q ^ 2 - 1) * w) := by
          rw [e]; ring
      _ = 2 ^ s * (m * d) := by rw [← h]; ring
  have e : q ^ 3 = 2 ^ s * b ^ 3 := by rw [hqab, ← h3a]; ring
  have hb3 : 0 < b ^ 3 := pow_pos hb.pos 3
  have hq3 : z ^ 3 ≤ q ^ 3 := by
    rw [← hz, e]
    exact Nat.le_mul_of_pos_right _ hb3
  have hzq : z ≤ q := (Nat.pow_le_pow_iff_left (by norm_num)).mp hq3
  have hsz := size_even hz16 hmc hc
  have hmono : (z ^ 2 - 1) * (z ^ 3 - 1) ≤ (q ^ 2 - 1) * w :=
    Nat.mul_le_mul (Nat.sub_le_sub_right (Nat.pow_le_pow_left hzq 2) 1)
      (le_trans (Nat.sub_le_sub_right (Nat.pow_le_pow_left hzq 3) 1) hwq)
  have hpos : 0 < 2 ^ s := by positivity
  have hcancel : m * d = b ^ 3 * ((q ^ 2 - 1) * w) := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    calc 2 ^ s * (m * d) = 2 ^ s * m * d := by ring
      _ = q ^ 3 * ((q ^ 2 - 1) * w) := h
      _ = 2 ^ s * (b ^ 3 * ((q ^ 2 - 1) * w)) := by rw [e]; ring
  have h1 : (q ^ 2 - 1) * w ≤ b ^ 3 * ((q ^ 2 - 1) * w) := Nat.le_mul_of_pos_left _ hb3
  have h2 : m * d ≤ 3 * m :=
    calc m * d ≤ m * 3 := Nat.mul_le_mul_left _ hd3
      _ = 3 * m := by ring
  omega

theorem not_eq_N_plus {s z m c q d : ℕ} (hs : 3 ≤ s) (hz : 2 ^ s = z ^ 3) (hz16 : 16 ≤ z)
    (hm : Odd m) (hmc : m ≤ c * z ^ 4) (hc : 12 * c < z) (hq : 2 ≤ q) (hd : Odd d)
    (hd3 : d ≤ 3) : 2 ^ s * m * d ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
  intro h
  rcases Nat.even_or_odd q with hqe | ⟨t, rfl⟩
  · exact even_final hz hz16 hm hmc hc hd hd3 hq hqe (odd_cube_of_even hq hqe).1 le_rfl h
  · obtain ⟨j, rfl⟩ : ∃ j, s = j + 3 := ⟨s - 3, by omega⟩
    have ht : 1 ≤ t := by omega
    have h' : (2 * t + 1) ^ 3 * (((2 * t + 1) ^ 2 - 1) * ((2 * t + 1) ^ 3 - 1)) =
        d * (2 ^ (j + 3) * m) := by rw [← h]; ring
    have h1 := odd_N_plus_bound ht (Dvd.intro _ rfl) h'
    have h2 : 2 ^ (j + 3) = 2 * 2 ^ (j + 2) := by ring
    have h3 : (2 * t + 1 + 1) ^ 2 = (2 * t + 2) ^ 2 := by ring
    exact odd_final (T := 2 ^ (j + 3)) hz hz16 hmc hc (by omega) hd3 (by omega) (le_of_eq h')

theorem not_eq_N_minus {s z m c q d : ℕ} (hs : 3 ≤ s) (hz : 2 ^ s = z ^ 3) (hz16 : 16 ≤ z)
    (hm : Odd m) (hmc : m ≤ c * z ^ 4) (hc : 12 * c < z) (hq : 2 ≤ q) (hd : Odd d)
    (hd3 : d ≤ 3) : 2 ^ s * m * d ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
  intro h
  rcases Nat.even_or_odd q with hqe | ⟨t, rfl⟩
  · exact even_final hz hz16 hm hmc hc hd hd3 hq hqe (odd_cube_of_even hq hqe).2
      (by omega) h
  · obtain ⟨j, rfl⟩ : ∃ j, s = j + 3 := ⟨s - 3, by omega⟩
    have ht : 1 ≤ t := by omega
    have h' : (2 * t + 1) ^ 3 * (((2 * t + 1) ^ 2 - 1) * ((2 * t + 1) ^ 3 + 1)) =
        d * (2 ^ (j + 3) * m) := by rw [← h]; ring
    have h1 := odd_N_minus_bound ht (Dvd.intro _ rfl) h'
    have h2 : 2 ^ (j + 3) = 2 * 2 ^ (j + 2) := by ring
    have h3 : (2 * t + 1 + 1) ^ 2 = (2 * t + 2) ^ 2 := by ring
    exact odd_final (T := 2 ^ (j + 3)) hz hz16 hmc hc (by omega) hd3 (by omega)
      ((N_plus_le_N_minus _).trans (le_of_eq h'))

theorem odd_gcd_three (x : ℕ) : Odd (Nat.gcd 3 x) := by
  rcases (Nat.dvd_prime Nat.prime_three).mp (Nat.gcd_dvd_left 3 x) with h | h <;> rw [h]
  · exact odd_one
  · exact ⟨1, by norm_num⟩

theorem gcd_three_le (x : ℕ) : Nat.gcd 3 x ≤ 3 :=
  Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 3 x)

theorem odd_pow_sub_one {y k : ℕ} (hy : Even y) (hy2 : 2 ≤ y) (hk : k ≠ 0) :
    Odd (y ^ k - 1) := by
  have h : Even (y ^ k) := Nat.even_pow.mpr ⟨hy, hk⟩
  have h1 : 1 ≤ y ^ k := Nat.one_le_pow _ _ (by omega)
  obtain ⟨r, hr⟩ := h
  exact ⟨r - 1, by omega⟩

theorem odd_pow_add_one {y k : ℕ} (hy : Even y) (hk : k ≠ 0) : Odd (y ^ k + 1) := by
  obtain ⟨r, hr⟩ : Even (y ^ k) := Nat.even_pow.mpr ⟨hy, hk⟩
  exact ⟨r, by omega⟩

end CFSG.Quasithin.S1421QA20
