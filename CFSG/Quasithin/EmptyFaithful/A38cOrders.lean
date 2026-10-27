module

public import CFSG.Quasithin.H13.VolIA38Orders
public import CFSG.Quasithin.Vol2.Ch10SecAShapeCard

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Timmesfeld.Orders CFSG.Quasithin.H13.VolI CFSG.Quasithin.Vol2.Ch10.SecA

theorem not_a38Order_of {m a b : ℕ} (hm : m = 2 ^ a * b) (hb : Odd b) (h3 : 3 ∣ b)
    (hne : b ≠ 4 ^ a - 1) (h168 : a = 3 → b ≠ 21) (hJ : m ≠ 175560)
    (hP : ∀ p : ℕ, p.Prime → 3 < p → ordA 1 p ≠ m) : ¬ A38Order m := by
  have hnot : ¬ ShapeCard m := hm ▸ not_shapeCard_of hb h3 (fun _ => hne) h168
  rintro (⟨n, hn, h⟩ | ⟨f, hf, hf3, h⟩ | h | ⟨p, hp, hp3, h⟩)
  · refine hnot (Or.inl ⟨n, hn, ?_⟩)
    rw [h, ordA_one_two_pow (by omega), ← pow_mul, mul_comm n 2, pow_mul]
    norm_num
  · obtain ⟨a', rfl⟩ := hf
    refine hnot (Or.inr (Or.inl ⟨a', by omega, ?_⟩))
    rw [h]
    unfold ordSuzuki
    ring
  · exact hJ h
  · exact hP p hp hp3 h.symm

theorem ordA_one_ne_of_lt {b B : ℕ} (hB : 2 * b < B * (B ^ 2 - 1))
    (hsmall : ∀ p : ℕ, p < B → p.Prime → 3 < p → p * (p ^ 2 - 1) ≠ 2 * b) (p : ℕ) (hp : p.Prime)
    (hp3 : 3 < p) : ordA 1 p ≠ b := by
  intro h
  have h2 := two_mul_ordA_one_of_odd (hp.odd_of_ne_two (by omega))
  rw [h] at h2
  by_cases hpB : p < B
  · exact hsmall p hpB hp hp3 h2.symm
  · have hB' : B ≤ p := by omega
    have : B * (B ^ 2 - 1) ≤ p * (p ^ 2 - 1) :=
      Nat.mul_le_mul hB' (Nat.sub_le_sub_right (Nat.pow_le_pow_left hB' 2) 1)
    omega

theorem not_a38Order_360 : ¬ A38Order 360 :=
  not_a38Order_of (a := 3) (b := 45) rfl (by decide) (by decide) (by decide) (by decide)
    (by decide)
    (ordA_one_ne_of_lt (b := 360) (B := 10) (by norm_num) (by
      intro p hpB hp hp3
      interval_cases p <;> first | decide | exact absurd hp (by decide)))

theorem not_a38Order_2520 : ¬ A38Order 2520 :=
  not_a38Order_of (a := 3) (b := 315) rfl (by decide) (by decide) (by decide) (by decide)
    (by decide)
    (ordA_one_ne_of_lt (b := 2520) (B := 18) (by norm_num) (by
      intro p hpB hp hp3
      interval_cases p <;> decide))

theorem not_a38Order_20160 : ¬ A38Order 20160 :=
  not_a38Order_of (a := 6) (b := 315) rfl (by decide) (by decide) (by decide) (by decide)
    (by decide)
    (fun p hp hp3 => ordA_one_ne_of_two_pow (N := 6) hp hp3 ⟨315, rfl⟩ (by norm_num))

theorem not_a38Order_9999360 : ¬ A38Order 9999360 :=
  not_a38Order_of (a := 10) (b := 9765) rfl (by decide) (by decide) (by decide) (by decide)
    (by decide)
    (fun p hp hp3 => ordA_one_ne_of_two_pow (N := 10) hp hp3 ⟨9765, rfl⟩ (by norm_num))

theorem not_shapeCard_1080 : ¬ ShapeCard 1080 :=
  not_shapeCard_of (a := 3) (b := 135) (by decide) (by decide) (fun _ => by decide)
    (fun _ => by decide)

theorem not_shapeCard_979200 : ¬ ShapeCard 979200 :=
  not_shapeCard_num (a := 8) (b := 3825) (by norm_num) (by decide) (by decide) (by decide)
    (by decide)

theorem not_a38Order_979200 : ¬ A38Order 979200 :=
  not_a38Order_of (a := 8) (b := 3825) rfl (by decide) (by decide) (by decide) (by decide)
    (by decide)
    (fun p hp hp3 => ordA_one_ne_of_two_pow (N := 8) hp hp3 ⟨3825, rfl⟩ (by norm_num))

theorem card_sl_two_ne_card_sl_three {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    2 ^ n * (4 ^ n - 1) ≠ 2 ^ (3 * m) * ((2 ^ (3 * m) - 1) * (2 ^ (2 * m) - 1)) := by
  intro h
  have hu : Odd (4 ^ n - 1) := by
    rw [show (4 : ℕ) ^ n = 2 ^ (2 * n) by
      rw [pow_mul]
      norm_num]
    exact Vol2.Ch10.SecA.odd_two_pow_sub_one (by omega)
  have hv : Odd ((2 ^ (3 * m) - 1) * (2 ^ (2 * m) - 1)) :=
    (Vol2.Ch10.SecA.odd_two_pow_sub_one (by omega)).mul
      (Vol2.Ch10.SecA.odd_two_pow_sub_one (by omega))
  obtain ⟨rfl, huv⟩ := two_pow_mul_odd_inj hu hv h
  have h4 : (4 : ℕ) ^ (3 * m) = (2 ^ (3 * m)) ^ 2 :=
    calc (4 : ℕ) ^ (3 * m) = (2 ^ 2) ^ (3 * m) := by norm_num
      _ = 2 ^ (2 * (3 * m)) := (pow_mul 2 2 (3 * m)).symm
      _ = (2 ^ (3 * m)) ^ 2 := pow_mul' 2 2 (3 * m)
  rw [h4] at huv
  have hPQ : 2 ^ (2 * m) ≤ 2 ^ (3 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hP1 : 1 ≤ 2 ^ (2 * m) := Nat.one_le_two_pow
  have hQ2 : 2 ≤ 2 ^ (3 * m) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (3 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
  generalize 2 ^ (2 * m) = P at hPQ hP1 huv
  generalize 2 ^ (3 * m) = Q at hPQ hQ2 huv
  have hQ1 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega)
  zify [hP1, hQ1, show 1 ≤ Q by omega] at huv
  nlinarith

end CFSG.Quasithin
