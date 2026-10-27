module

public import CFSG.Quasithin.Vol2.Ch1EightFourNum
import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.Quasithin.Ch1Four

structure FixShape (m : ℕ) : Prop where
  fin : ∀ c ∈ finOrders, ∀ k, m * 2 ^ k ≠ c
  three : 3 ∣ m
  two : ∀ n, m ≠ 2 ^ n * (4 ^ n - 1)
  odd : ∀ p A k : ℕ, p.Prime → 5 ≤ p → Odd A → p ∣ A → m * 2 ^ k ≠ A * (p ^ 2 - 1)

structure FixShapeC (m : ℕ) : Prop where
  fin : ∀ c ∈ finOrders, ∀ k, m * 2 ^ k ≠ c
  three : 3 ∣ m
  two : ∀ n, m ≠ 2 ^ n * (4 ^ n - 1)
  odd : ∀ p c k : ℕ, p.Prime → 5 ≤ p → (c = 1 ∨ c = 3) → m * 2 ^ k ≠ c * (p * (p ^ 2 - 1))

theorem two_false_of {m b o : ℕ} (hm : m = 2 ^ b * o) (ho : Odd o) (hne : o ≠ 4 ^ b - 1) :
    ∀ n, m ≠ 2 ^ n * (4 ^ n - 1) := by
  intro n h
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [pow_zero, Nat.sub_self, mul_zero] at h
    rw [h] at hm
    have : o = 0 := by
      rcases Nat.eq_zero_or_pos o with h0 | h0
      · exact h0
      · have := Nat.mul_pos (Nat.two_pow_pos b) h0
        omega
    rw [this] at ho
    exact absurd ho (by decide)
  · have hodd4 : Odd (4 ^ n - 1) := by
      have : Even (4 ^ n) := (Nat.even_pow' (by omega)).mpr (by decide)
      exact Nat.Even.sub_odd (Nat.one_le_pow _ _ (by norm_num)) this odd_one
    obtain ⟨h1, h2⟩ := two_pow_mul_odd_inj ho hodd4 (hm.symm.trans h)
    rw [h1] at hne
    exact hne h2

theorem odd_false_of {m b : ℕ} (L : List ℕ) (hL : ∀ q ∈ L, q.Prime) (hm : m = L.prod)
    (hb : 2 ^ b ∣ m) (hbad : ∀ p ∈ L, 5 ≤ p → ¬ 2 ^ b ∣ p ^ 2 - 1) :
    ∀ p A k : ℕ, p.Prime → 5 ≤ p → Odd A → p ∣ A → m * 2 ^ k ≠ A * (p ^ 2 - 1) := by
  intro p A k hp hp5 hA hpA h
  have hpm : p ∣ m := prime_dvd_of_dvd_mul_two_pow hp (by omega) (h ▸ hpA.mul_right _)
  rw [hm] at hpm
  have hpL := mem_of_prime_dvd_prod hp L hL hpm
  have h2 : 2 ^ b ∣ A * (p ^ 2 - 1) := h ▸ hb.mul_right _
  exact hbad p hpL hp5 ((coprime_two_pow_of_odd b hA).dvd_of_dvd_mul_left h2)

theorem false_of_odd_parts {m c0 N k a b o0 o1 : ℕ} (hm : m = 2 ^ b * o1) (hc : c0 = 2 ^ a * o0)
    (ho0 : Odd o0) (ho1 : Odd o1) (hN : Odd N) (h : m * 2 ^ k = N * c0) (hne : o1 ≠ N * o0) :
    False := by
  have e : 2 ^ (b + k) * o1 = 2 ^ a * (N * o0) := by
    calc 2 ^ (b + k) * o1 = m * 2 ^ k := by rw [hm, pow_add]; ring
      _ = N * c0 := h
      _ = 2 ^ a * (N * o0) := by rw [hc]; ring
  exact hne (two_pow_mul_odd_inj ho1 (hN.mul ho0) e).2

theorem fixShape_m11 : FixShape 7920 where
  fin := not_fin_of_odd (a := 4) (o := 495) (by norm_num) (by decide) (by decide)
  three := by norm_num
  two := two_false_of (b := 4) (o := 495) (by norm_num) (by decide) (by norm_num)
  odd := odd_false_of [2, 2, 2, 2, 3, 3, 5, 11] (by decide) (by norm_num) (b := 4) (by norm_num)
    (by decide)

theorem fixShape_m12 : FixShape 95040 where
  fin := not_fin_of_odd (a := 6) (o := 1485) (by norm_num) (by decide) (by decide)
  three := by norm_num
  two := two_false_of (b := 6) (o := 1485) (by norm_num) (by decide) (by norm_num)
  odd := odd_false_of [2, 2, 2, 2, 2, 2, 3, 3, 3, 5, 11] (by decide) (by norm_num) (b := 6)
    (by norm_num) (by decide)

theorem fixShape_m23 : FixShape 10200960 where
  fin := not_fin_of_odd (a := 7) (o := 79695) (by norm_num) (by decide) (by decide)
  three := by norm_num
  two := two_false_of (b := 7) (o := 79695) (by norm_num) (by decide) (by norm_num)
  odd := odd_false_of [2, 2, 2, 2, 2, 2, 2, 3, 3, 5, 7, 11, 23] (by decide) (by norm_num) (b := 7)
    (by norm_num) (by decide)

theorem fixShape_j2 : FixShape 604800 where
  fin := not_fin_of_odd (a := 7) (o := 4725) (by norm_num) (by decide) (by decide)
  three := by norm_num
  two := two_false_of (b := 7) (o := 4725) (by norm_num) (by decide) (by norm_num)
  odd := odd_false_of [2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 5, 5, 7] (by decide) (by norm_num) (b := 7)
    (by norm_num) (by decide)

theorem fixShape_j4 : FixShape 86775571046077562880 where
  fin := not_fin_of_odd (a := 21) (o := 41377816699065) (by norm_num) (by decide) (by decide)
  three := by norm_num
  two := two_false_of (b := 21) (o := 41377816699065) (by norm_num) (by decide) (by norm_num)
  odd := odd_false_of ([2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] ++
    [3, 3, 3, 5, 7, 11, 11, 11, 23, 29, 31, 37, 43]) (by decide) (by norm_num) (b := 21)
    (by norm_num) (by decide)

theorem fixShape_hs : FixShape 44352000 where
  fin := not_fin_of_odd (a := 9) (o := 86625) (by norm_num) (by decide) (by decide)
  three := by norm_num
  two := two_false_of (b := 9) (o := 86625) (by norm_num) (by decide) (by norm_num)
  odd := odd_false_of [2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 5, 5, 5, 7, 11] (by decide) (by norm_num)
    (b := 9) (by norm_num) (by decide)

theorem fixShape_he : FixShape 4030387200 where
  fin := not_fin_of_odd (a := 10) (o := 3935925) (by norm_num) (by decide) (by decide)
  three := by norm_num
  two := two_false_of (b := 10) (o := 3935925) (by norm_num) (by decide) (by norm_num)
  odd := odd_false_of [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 5, 5, 7, 7, 7, 17] (by decide)
    (by norm_num) (b := 10) (by norm_num) (by decide)

theorem fixShape_ru : FixShape 145926144000 where
  fin := not_fin_of_odd (a := 14) (o := 8906625) (by norm_num) (by decide) (by decide)
  three := by norm_num
  two := two_false_of (b := 14) (o := 8906625) (by norm_num) (by decide) (by norm_num)
  odd := odd_false_of [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 5, 5, 5, 7, 13, 29]
    (by decide) (by norm_num) (b := 14) (by norm_num) (by decide)

theorem fixShape_l52 : FixShape 9999360 where
  fin := not_fin_of_odd (a := 10) (o := 9765) (by norm_num) (by decide) (by decide)
  three := by norm_num
  two := two_false_of (b := 10) (o := 9765) (by norm_num) (by decide) (by norm_num)
  odd := odd_false_of [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 5, 7, 31] (by decide) (by norm_num)
    (b := 10) (by norm_num) (by decide)

theorem fixShape_tits : FixShape 17971200 where
  fin := not_fin_of_odd (a := 11) (o := 8775) (by norm_num) (by decide) (by decide)
  three := by norm_num
  two := two_false_of (b := 11) (o := 8775) (by norm_num) (by decide) (by norm_num)
  odd := odd_false_of [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 5, 5, 13] (by decide)
    (by norm_num) (b := 11) (by norm_num) (by decide)

theorem prime_mem_of_dvd {m p k A : ℕ} (L : List ℕ) (hL : ∀ q ∈ L, q.Prime) (hm : m = L.prod)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpA : p ∣ A) (h : m * 2 ^ k = A) : p ∈ L := by
  have hpm : p ∣ m := prime_dvd_of_dvd_mul_two_pow hp (by omega) (h ▸ hpA)
  rw [hm] at hpm
  exact mem_of_prime_dvd_prod hp L hL hpm

theorem fixShapeC_hatA7 : FixShapeC 7560 where
  fin := not_fin_of_odd (a := 3) (o := 945) (by norm_num) (by decide) (by decide)
  three := by norm_num
  two := two_false_of (b := 3) (o := 945) (by norm_num) (by decide) (by norm_num)
  odd := by
    intro p c k hp hp5 hc h
    have hpL := prime_mem_of_dvd [2, 2, 2, 3, 3, 3, 5, 7] (by decide) (by norm_num) hp hp5
      (dvd_mul_of_dvd_right (dvd_mul_right p _) c) h
    have hcodd : Odd c := by rcases hc with rfl | rfl <;> decide
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpL
    rcases hpL with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals omega

theorem fixShapeC_j1 : FixShapeC 175560 where
  fin := not_fin_of_odd (a := 3) (o := 21945) (by norm_num) (by decide) (by decide)
  three := by norm_num
  two := two_false_of (b := 3) (o := 21945) (by norm_num) (by decide) (by norm_num)
  odd := by
    intro p c k hp hp5 hc h
    have hpL := prime_mem_of_dvd [2, 2, 2, 3, 5, 7, 11, 19] (by decide) (by norm_num) hp hp5
      (dvd_mul_of_dvd_right (dvd_mul_right p _) c) h
    have hcodd : Odd c := by rcases hc with rfl | rfl <;> decide
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpL
    rcases hpL with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals omega

end CFSG.Quasithin.Ch1Four
