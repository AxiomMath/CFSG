module

public import CFSG.Quasithin.Vol2.Ch10SecKIK2q

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem odd_pow_sub_one' {f k : ℕ} (hf : 1 ≤ f) (hk : 1 ≤ k) : Odd ((2 ^ f) ^ k - 1) :=
  CFSG.Timmesfeld.Orders.odd_pow_sub_one (by omega) (by omega)

theorem odd_part_lt {x k : ℕ} (hx : 2 ≤ x) (hk : 3 ≤ k) :
    (x ^ 2 - 1) * (x ^ k - 1) < (x ^ k) ^ 2 - 1 := by
  have h1 : 4 ≤ x ^ 2 := by nlinarith
  have h2 : x ^ 2 < x ^ k := Nat.pow_lt_pow_right (by omega) (by omega)
  have h3 : 1 ≤ x ^ k := by omega
  have h4 : (x ^ k) ^ 2 - 1 = (x ^ k - 1) * (x ^ k + 1) := by
    zify [h3, Nat.one_le_pow 2 (x ^ k) (by omega)]
    ring
  rw [h4, mul_comm (x ^ k - 1)]
  exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)

section Orders

variable {X : Type} [Group X]

theorem card_of_isPSL3 {f : ℕ} (hf : 1 ≤ f) (h : IsPSL 3 2 f X) : ∃ u : ℕ, Odd u ∧
    Nat.card X = 2 ^ (3 * f) * u ∧ (u = ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 - 1) ∨
      3 * u = ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 - 1)) := by
  have hX := (CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl
  have hA : Odd (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 - 1)) :=
    (odd_pow_sub_one' hf (by norm_num)).mul (odd_pow_sub_one' hf (by norm_num))
  have hI : Finset.Icc 2 (2 + 1) = {2, 3} := by decide
  have e3 : (2 : ℕ) ^ (3 * f) = (2 ^ f) ^ 3 := by rw [← pow_mul, mul_comm]
  rw [ordA, hI, Finset.prod_pair (by norm_num), show 2 * (2 + 1) / 2 = 3 by norm_num] at hX
  have hg : Nat.gcd (2 + 1) (2 ^ f - 1) ∣ ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 - 1) :=
    (Nat.gcd_dvd_right _ _).trans (Dvd.dvd.mul_left (Nat.sub_one_dvd_pow_sub_one (2 ^ f) 3) _)
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp (Nat.gcd_dvd_left 3 (2 ^ f - 1)) with
    h1 | h1 <;> rw [show 2 + 1 = 3 by norm_num] at hX hg <;> rw [h1] at hX hg
  · exact ⟨_, hA, by rw [hX, Nat.div_one, e3], Or.inl rfl⟩
  · obtain ⟨u, hu⟩ := hg
    refine ⟨u, ?_, ?_, Or.inr hu.symm⟩
    · rw [hu] at hA
      exact (Nat.odd_mul.mp hA).2
    · rw [hX, hu, e3, mul_comm 3 u, ← mul_assoc, Nat.mul_div_cancel _ (by norm_num)]

theorem card_of_isSL3 {f : ℕ} (h : IsSL3 (2 ^ f) X) :
    Nat.card X = 2 ^ (3 * f) * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 - 1)) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, card_statedSL_three1527d, hK, ← pow_mul, mul_comm f 3]

theorem card_of_isPSp4 {f : ℕ} (hf : 1 ≤ f) (h : IsPSp4 2 f X) :
    Nat.card X = 2 ^ (4 * f) * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 4 - 1)) := by
  have hX := (CFSG.Timmesfeld.card_statedClassicalModel_two h).2.2.1 rfl
  have hI : Finset.Icc 1 2 = {1, 2} := by decide
  have hg : Nat.gcd 2 (2 ^ f - 1) = 1 := by
    have := (odd_pow_sub_one' (k := 1) hf le_rfl)
    rw [pow_one] at this
    exact (Nat.coprime_two_left).mpr this
  rw [ordBC, hI, Finset.prod_pair (by norm_num), hg, Nat.div_one, mul_one,
    show 2 * 2 = 4 by norm_num] at hX
  rw [hX, ← pow_mul, mul_comm f 4]

end Orders

section TwoAdic


variable {X : Type} [Group X]

theorem card_of_isG2 {f : ℕ} (h : IsG2 2 f X) :
    Nat.card X = 2 ^ (6 * f) * (((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 2 - 1)) := by
  have hX := CFSG.Timmesfeld.card_chevalleyExceptionalModel_two h
  simp only [ordG2] at hX
  rw [hX, ← pow_mul, mul_comm f 6, mul_assoc]

theorem goodLie_two_adic (hG : GoodLie X) : ∃ f u : ℕ, Odd u ∧
    ((1 ≤ f ∧ Nat.card X = 2 ^ (3 * f) * u ∧
        (u = ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 - 1) ∨
          3 * u = ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 - 1))) ∨
      (2 ≤ f ∧ Nat.card X = 2 ^ (4 * f) * u ∧ u = ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 4 - 1)) ∨
      (2 ≤ f ∧ Nat.card X = 2 ^ (6 * f) * u ∧ u = ((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 2 - 1))) := by
  obtain ⟨f, ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩⟩ := hG
  · obtain ⟨u, hu, hc, h'⟩ := card_of_isPSL3 hf h
    exact ⟨f, u, hu, Or.inl ⟨hf, hc, h'⟩⟩
  · exact ⟨f, _, (odd_pow_sub_one' hf (by norm_num)).mul (odd_pow_sub_one' hf (by norm_num)),
      Or.inl ⟨hf, card_of_isSL3 h, Or.inl rfl⟩⟩
  · exact ⟨f, _, (odd_pow_sub_one' (by omega) (by norm_num)).mul
      (odd_pow_sub_one' (by omega) (by norm_num)),
      Or.inr (Or.inl ⟨hf, card_of_isPSp4 (by omega) h, rfl⟩)⟩
  · exact ⟨f, _, (odd_pow_sub_one' (by omega) (by norm_num)).mul
      (odd_pow_sub_one' (by omega) (by norm_num)), Or.inr (Or.inr ⟨hf, card_of_isG2 h, rfl⟩)⟩

theorem false_of_two_adic (hG : GoodLie X) {N v u₀ : ℕ}
    (hX : Nat.card X = N ∨ Nat.card X = 3 * N) (hN : N = 2 ^ v * u₀) (hu₀ : Odd u₀)
    (h3 : ∀ f, 1 ≤ f → 3 * f = v → ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 - 1) ≠ u₀ ∧
      ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 - 1) ≠ 3 * u₀ ∧
      ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 - 1) ≠ 9 * u₀)
    (h4 : ∀ f, 2 ≤ f → 4 * f = v → ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 4 - 1) ≠ u₀ ∧
      ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 4 - 1) ≠ 3 * u₀)
    (h6 : ∀ f, 2 ≤ f → 6 * f = v → ((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 2 - 1) ≠ u₀ ∧
      ((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 2 - 1) ≠ 3 * u₀) : False := by
  obtain ⟨f, u, hu, h⟩ := goodLie_two_adic hG
  have hu3 : Odd (3 * u₀) := (by decide : Odd 3).mul hu₀
  have key : ∀ k, Nat.card X = 2 ^ (k * f) * u → k * f = v ∧ (u = u₀ ∨ u = 3 * u₀) := by
    intro k hk
    rcases hX with h1 | h1
    · obtain ⟨e1, e2⟩ := eq_and_eq_of_two_pow_mul hu hu₀ (hk.symm.trans (h1.trans hN))
      exact ⟨e1, Or.inl e2⟩
    · have : Nat.card X = 2 ^ v * (3 * u₀) := by rw [h1, hN]; ring
      obtain ⟨e1, e2⟩ := eq_and_eq_of_two_pow_mul hu hu3 (hk.symm.trans this)
      exact ⟨e1, Or.inr e2⟩
  rcases h with ⟨hf, hc, hA | hA⟩ | ⟨hf, hc, hA⟩ | ⟨hf, hc, hA⟩
  · obtain ⟨hv, hu' | hu'⟩ := key 3 hc
    · exact (h3 f hf hv).1 (hA.symm.trans hu')
    · exact (h3 f hf hv).2.1 (hA.symm.trans hu')
  · obtain ⟨hv, hu' | hu'⟩ := key 3 hc
    · exact (h3 f hf hv).2.1 (by rw [← hA, hu'])
    · exact (h3 f hf hv).2.2 (by rw [← hA, hu']; ring)
  · obtain ⟨hv, hu' | hu'⟩ := key 4 hc
    · exact (h4 f hf hv).1 (hA.symm.trans hu')
    · exact (h4 f hf hv).2 (hA.symm.trans hu')
  · obtain ⟨hv, hu' | hu'⟩ := key 6 hc
    · exact (h6 f hf hv).1 (hA.symm.trans hu')
    · exact (h6 f hf hv).2 (hA.symm.trans hu')

theorem false_of_sl2_order (hG : GoodLie X) {a : ℕ} (ha : 1 ≤ a)
    (hX : Nat.card X = 2 ^ a * ((2 ^ a) ^ 2 - 1) ∨
      Nat.card X = 3 * (2 ^ a * ((2 ^ a) ^ 2 - 1))) : False := by
  have hx : ∀ f, 1 ≤ f → 2 ≤ 2 ^ f := fun f hf => by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hlt : ∀ f k, 1 ≤ f → 3 ≤ k → k * f = a →
      ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ k - 1) < (2 ^ a) ^ 2 - 1 := fun f k hf hk hka => by
    rw [← hka, show (2 : ℕ) ^ (k * f) = (2 ^ f) ^ k by rw [← pow_mul, mul_comm]]
    exact odd_part_lt (hx f hf) hk
  refine false_of_two_adic hG hX rfl (odd_pow_sub_one' ha (by norm_num)) ?_ ?_ ?_
  · intro f hf hv
    have := hlt f 3 hf le_rfl (by omega)
    refine ⟨by omega, by omega, by omega⟩
  · intro f hf hv
    have := hlt f 4 (by omega) (by norm_num) (by omega)
    exact ⟨by omega, by omega⟩
  · intro f hf hv
    have := hlt f 6 (by omega) (by norm_num) (by omega)
    rw [mul_comm ((2 ^ f) ^ 2 - 1) ((2 ^ f) ^ 6 - 1)] at this
    exact ⟨by omega, by omega⟩

end TwoAdic

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
