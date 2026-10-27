module

public import CFSG.Quasithin.EmptyFaithful.A38cOrders
public import CFSG.Quasithin.Vol2.Ch1EightFourFixed
public import CFSG.Quasithin.Vol2.Ch1EightFourOdd

public section

namespace CFSG.Quasithin.Ch1Two

open CFSG.Open CFSG.Quasithin.H13.VolI CFSG.Quasithin.Ch1Four

theorem two_pow_sq_eq_four_pow (n : ℕ) : (2 ^ n) ^ 2 = 4 ^ n := by
  rw [← pow_mul, mul_comm, pow_mul]
  norm_num

theorem five_le_of_three_lt {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) : 5 ≤ p := by
  by_contra h
  have h4 : p = 4 := by omega
  subst h4
  exact absurd hp (by decide)

theorem sixty_le_of_a38Order {m : ℕ} (h : A38Order m) : 60 ≤ m := by
  rcases h with ⟨n, hn, rfl⟩ | ⟨f, -, hf3, rfl⟩ | rfl | ⟨p, hp, hp3, rfl⟩
  · rw [ordA_one_two_pow (by omega)]
    have hq : 4 ≤ 2 ^ n :=
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    generalize 2 ^ n = q at hq ⊢
    have h16 : 16 ≤ q ^ 2 := by nlinarith
    have h15 : 15 ≤ q ^ 2 - 1 := by omega
    nlinarith
  · have hq : 8 ≤ 2 ^ f :=
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf3
    unfold ordSuzuki
    generalize 2 ^ f = q at hq ⊢
    have h64 : 64 ≤ q ^ 2 := by nlinarith
    have h1 : 1 ≤ (q ^ 2 + 1) * (q - 1) := Nat.one_le_iff_ne_zero.mpr (by
      apply Nat.mul_ne_zero <;> omega)
    calc 60 ≤ q ^ 2 * 1 := by omega
      _ ≤ q ^ 2 * ((q ^ 2 + 1) * (q - 1)) := Nat.mul_le_mul_left _ h1
      _ = q ^ 2 * (q ^ 2 + 1) * (q - 1) := by ring
  · norm_num
  · have h2 := two_mul_ordA_one_of_odd (hp.odd_of_ne_two (by omega))
    have hp5 := five_le_of_three_lt hp hp3
    have h25 : 25 ≤ p ^ 2 := by nlinarith
    have h24 : 24 ≤ p ^ 2 - 1 := by omega
    have : 120 ≤ p * (p ^ 2 - 1) := by nlinarith
    omega

theorem even_of_a38Order {m : ℕ} (h : A38Order m) : Even m := by
  rcases h with ⟨n, hn, rfl⟩ | ⟨f, -, hf3, rfl⟩ | rfl | ⟨p, hp, hp3, rfl⟩
  · rw [ordA_one_two_pow (by omega)]
    exact (Nat.even_pow.mpr ⟨even_two, by omega⟩).mul_right _
  · unfold ordSuzuki
    exact ((Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, by omega⟩, by norm_num⟩).mul_right
      _).mul_right _
  · decide
  · obtain ⟨k, hk⟩ := hp.odd_of_ne_two (by omega)
    have h2 := two_mul_ordA_one_of_odd (p := p) ⟨k, hk⟩
    subst hk
    have hsq : (2 * k + 1) ^ 2 - 1 = 4 * (k * (k + 1)) := by
      have : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
      omega
    rw [hsq] at h2
    have hm : ordA 1 (2 * k + 1) = (2 * k + 1) * (2 * (k * (k + 1))) := by
      have : 2 * ordA 1 (2 * k + 1) = 2 * ((2 * k + 1) * (2 * (k * (k + 1)))) := by
        rw [h2]
        ring
      omega
    rw [hm]
    exact (even_two_mul _).mul_left _

theorem false_of_a38Order {m : ℕ} (hA : A38Order m) (h3 : 3 ∣ m) (hJ : m ≠ 175560)
    (hL2 : ∀ n, 2 ≤ n → m ≠ 2 ^ n * (4 ^ n - 1))
    (hP : ∀ p : ℕ, p.Prime → 3 < p → ordA 1 p ≠ m) : False := by
  rcases hA with ⟨n, hn, rfl⟩ | ⟨f, hf, -, rfl⟩ | rfl | ⟨p, hp, hp3, rfl⟩
  · apply hL2 n hn
    rw [ordA_one_two_pow (by omega), two_pow_sq_eq_four_pow]
  · obtain ⟨a, rfl⟩ := hf
    exact not_three_dvd_sz a h3
  · exact hJ rfl
  · exact hP p hp hp3 rfl

theorem mul_two_of_ordA_one {p m : ℕ} (hp : p.Prime) (hp3 : 3 < p) (h : ordA 1 p = m) :
    m * 2 ^ 1 = p * (p ^ 2 - 1) := by
  have h2 := two_mul_ordA_one_of_odd (hp.odd_of_ne_two (by omega))
  rw [h] at h2
  rw [pow_one, mul_comm]
  exact h2

theorem not_a38Order_of_fixShape {m : ℕ} (hF : FixShape m) (hJ : m ≠ 175560) : ¬ A38Order m :=
  fun hA => false_of_a38Order hA hF.three hJ (fun n _ => hF.two n) fun p hp hp3 h =>
    hF.odd p p 1 hp (five_le_of_three_lt hp hp3) (hp.odd_of_ne_two (by omega)) dvd_rfl
      (mul_two_of_ordA_one hp hp3 h)

theorem not_a38Order_443520 : ¬ A38Order 443520 :=
  not_a38Order_of (a := 7) (b := 3465) rfl (by decide) (by decide) (by decide) (by decide)
    (by decide)
    (fun p hp hp3 => ordA_one_ne_of_two_pow (N := 7) hp hp3 ⟨3465, rfl⟩ (by norm_num))

theorem not_a38Order_244823040 : ¬ A38Order 244823040 :=
  not_a38Order_of (a := 10) (b := 239085) rfl (by decide) (by decide) (by decide) (by decide)
    (by decide)
    (fun p hp hp3 => ordA_one_ne_of_two_pow (N := 10) hp hp3 ⟨239085, rfl⟩ (by norm_num))

theorem not_a38Order_of_r2 {r m : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hm : 2 * m = r ^ 2 * (r ^ 4 - 1)) : ¬ A38Order m := by
  intro hA
  refine false_of_a38Order hA (r2_three hr hr5 hm) ?_ (fun n hn h => r2_false_two hr hr5 hm hn h)
    fun p hp hp3 h => r2_false_p hr hr5 hm hp (five_le_of_three_lt hp hp3) (Or.inl rfl)
      (by rw [one_mul]; exact mul_two_of_ordA_one hp hp3 h)
  rintro rfl
  have hr11 : r < 11 := by
    by_contra hge
    have h1 : 11 ^ 2 ≤ r ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h2 : 11 ^ 4 - 1 ≤ r ^ 4 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left (by omega) 4) 1
    have h3 := Nat.mul_le_mul h1 h2
    norm_num at h3
    omega
  interval_cases r <;> first | exact absurd hr (by decide) | omega

theorem not_a38Order_of_oddL3Shape {m : ℕ} (h : OddL3Shape m) : ¬ A38Order m := by
  intro hA
  refine false_of_a38Order hA h.three ?_ (fun n hn hm => h.false_of_two hn hm)
    fun p hp hp3 h' => h.false_of_p hp (five_le_of_three_lt hp hp3) (Or.inl rfl)
      (by rw [one_mul]; exact mul_two_of_ordA_one hp hp3 h')
  obtain ⟨p, -, -, hp, hp3, -, -, -, -, -, hp3m, -⟩ := h.facts
  rintro rfl
  have hle : p ^ 3 ≤ 175560 := Nat.le_of_dvd (by norm_num) hp3m
  have hp57 : p < 57 := by
    by_contra hge
    have : 57 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left (by omega) 3
    omega
  interval_cases p <;> first | exact absurd hp (by decide) | exact absurd hp3m (by decide)

end CFSG.Quasithin.Ch1Two
