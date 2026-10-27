module

public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Quasithin.Gold14610

@[expose] def F618OrdA (y : ℕ) : Prop :=
  (∃ q, 11 ≤ q ∧ (q % 8 = 3 ∨ q % 8 = 5) ∧ y = q * (q ^ 2 - 1) / 2) ∨
  (∃ q, 7 ≤ q ∧ (q % 16 = 7 ∨ q % 16 = 9) ∧ y = q * (q ^ 2 - 1) / 2) ∨
  y = 1080 ∨ y = 2520 ∨ y = 7560 ∨
  (∃ p e, 3 ≤ p ∧ (e = 1 ∨ e = 3) ∧
    ((p % 8 = 5 ∧ y * e = p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 - 1))) ∨
     (p % 8 = 3 ∧ y * e = p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 + 1)))))

@[expose] def F618Ord (y : ℕ) : Prop := F618OrdA y ∨ y = 95040

theorem odd_mul_three {a b c : ℕ} (ha : Odd a) (hb : Odd b) (hc : Odd c) : Odd (a * (b * c)) :=
  Nat.odd_mul.mpr ⟨ha, Nat.odd_mul.mpr ⟨hb, hc⟩⟩

theorem psl_card_four {q : ℕ} (hq : q % 8 = 3 ∨ q % 8 = 5) :
    ∃ w, Odd w ∧ q * (q ^ 2 - 1) / 2 = 2 ^ 2 * w := by
  obtain ⟨k, hk⟩ : ∃ k, q = 8 * k + 3 ∨ q = 8 * k + 5 := ⟨q / 8, by omega⟩
  rcases hk with rfl | rfl
  · have h : (8 * k + 3) ^ 2 - 1 = 8 * ((4 * k + 1) * (2 * k + 1)) := by
      have : (8 * k + 3) ^ 2 = 8 * ((4 * k + 1) * (2 * k + 1)) + 1 := by ring
      omega
    refine ⟨(8 * k + 3) * ((4 * k + 1) * (2 * k + 1)), ?_, ?_⟩
    · exact odd_mul_three ⟨4 * k + 1, by ring⟩ ⟨2 * k, by ring⟩ ⟨k, by ring⟩
    · rw [h]
      exact Nat.div_eq_of_eq_mul_left (by norm_num) (by ring)
  · have h : (8 * k + 5) ^ 2 - 1 = 8 * ((2 * k + 1) * (4 * k + 3)) := by
      have : (8 * k + 5) ^ 2 = 8 * ((2 * k + 1) * (4 * k + 3)) + 1 := by ring
      omega
    refine ⟨(8 * k + 5) * ((2 * k + 1) * (4 * k + 3)), ?_, ?_⟩
    · exact odd_mul_three ⟨4 * k + 2, by ring⟩ ⟨k, by ring⟩ ⟨2 * k + 1, by ring⟩
    · rw [h]
      exact Nat.div_eq_of_eq_mul_left (by norm_num) (by ring)

theorem psl_card_eight {q : ℕ} (hq : q % 16 = 7 ∨ q % 16 = 9) :
    ∃ w, Odd w ∧ q * (q ^ 2 - 1) / 2 = 2 ^ 3 * w := by
  obtain ⟨k, hk⟩ : ∃ k, q = 16 * k + 7 ∨ q = 16 * k + 9 := ⟨q / 16, by omega⟩
  rcases hk with rfl | rfl
  · have h : (16 * k + 7) ^ 2 - 1 = 16 * ((8 * k + 3) * (2 * k + 1)) := by
      have : (16 * k + 7) ^ 2 = 16 * ((8 * k + 3) * (2 * k + 1)) + 1 := by ring
      omega
    refine ⟨(16 * k + 7) * ((8 * k + 3) * (2 * k + 1)), ?_, ?_⟩
    · exact odd_mul_three ⟨8 * k + 3, by ring⟩ ⟨4 * k + 1, by ring⟩ ⟨k, by ring⟩
    · rw [h]
      exact Nat.div_eq_of_eq_mul_left (by norm_num) (by ring)
  · have h : (16 * k + 9) ^ 2 - 1 = 16 * ((2 * k + 1) * (8 * k + 5)) := by
      have : (16 * k + 9) ^ 2 = 16 * ((2 * k + 1) * (8 * k + 5)) + 1 := by ring
      omega
    refine ⟨(16 * k + 9) * ((2 * k + 1) * (8 * k + 5)), ?_, ?_⟩
    · exact odd_mul_three ⟨8 * k + 4, by ring⟩ ⟨k, by ring⟩ ⟨4 * k + 2, by ring⟩
    · rw [h]
      exact Nat.div_eq_of_eq_mul_left (by norm_num) (by ring)

theorem l3_card_minus {p : ℕ} (hp : p % 8 = 5) :
    ∃ w, Odd w ∧ p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 - 1)) = 2 ^ 5 * w := by
  obtain ⟨k, rfl⟩ : ∃ k, p = 8 * k + 5 := ⟨p / 8, by omega⟩
  have h2 : (8 * k + 5) ^ 2 - 1 = 8 * ((2 * k + 1) * (4 * k + 3)) := by
    have : (8 * k + 5) ^ 2 = 8 * ((2 * k + 1) * (4 * k + 3)) + 1 := by ring
    omega
  have h3 : (8 * k + 5) ^ 3 - 1 = 4 * ((2 * k + 1) * (64 * k ^ 2 + 88 * k + 31)) := by
    have : (8 * k + 5) ^ 3 = 4 * ((2 * k + 1) * (64 * k ^ 2 + 88 * k + 31)) + 1 := by ring
    omega
  refine ⟨(8 * k + 5) ^ 3 * (((2 * k + 1) * (4 * k + 3)) *
    ((2 * k + 1) * (64 * k ^ 2 + 88 * k + 31))), ?_, ?_⟩
  · refine Nat.odd_mul.mpr ⟨Odd.pow ⟨4 * k + 2, by ring⟩, Nat.odd_mul.mpr
      ⟨Nat.odd_mul.mpr ⟨⟨k, by ring⟩, ⟨2 * k + 1, by ring⟩⟩, Nat.odd_mul.mpr
        ⟨⟨k, by ring⟩, ⟨32 * k ^ 2 + 44 * k + 15, by ring⟩⟩⟩⟩
  · rw [h2, h3]; ring

theorem l3_card_plus {p : ℕ} (hp : p % 8 = 3) :
    ∃ w, Odd w ∧ p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 + 1)) = 2 ^ 5 * w := by
  obtain ⟨k, rfl⟩ : ∃ k, p = 8 * k + 3 := ⟨p / 8, by omega⟩
  have h2 : (8 * k + 3) ^ 2 - 1 = 8 * ((4 * k + 1) * (2 * k + 1)) := by
    have : (8 * k + 3) ^ 2 = 8 * ((4 * k + 1) * (2 * k + 1)) + 1 := by ring
    omega
  have h3 : (8 * k + 3) ^ 3 + 1 = 4 * ((2 * k + 1) * (64 * k ^ 2 + 40 * k + 7)) := by ring
  refine ⟨(8 * k + 3) ^ 3 * (((4 * k + 1) * (2 * k + 1)) *
    ((2 * k + 1) * (64 * k ^ 2 + 40 * k + 7))), ?_, ?_⟩
  · refine Nat.odd_mul.mpr ⟨Odd.pow ⟨4 * k + 1, by ring⟩, Nat.odd_mul.mpr
      ⟨Nat.odd_mul.mpr ⟨⟨2 * k, by ring⟩, ⟨k, by ring⟩⟩, Nat.odd_mul.mpr
        ⟨⟨k, by ring⟩, ⟨32 * k ^ 2 + 20 * k + 3, by ring⟩⟩⟩⟩
  · rw [h2, h3]; ring

theorem two_adic_of_mul {y e W : ℕ} (he : e = 1 ∨ e = 3) (hW : Odd W) (h : y * e = 2 ^ 5 * W) :
    ∃ w, Odd w ∧ y = 2 ^ 5 * w := by
  rcases hW with ⟨m, rfl⟩
  rcases he with rfl | rfl
  · exact ⟨2 * m + 1, ⟨m, rfl⟩, by omega⟩
  · exact ⟨y / 32, ⟨(y / 32 - 1) / 2, by omega⟩, by omega⟩

theorem F618OrdA.two_adic {y : ℕ} (h : F618OrdA y) :
    ∃ a w, Odd w ∧ y = 2 ^ a * w ∧ (a = 2 ∨ a = 3 ∨ a = 5) := by
  rcases h with ⟨q, -, hq, rfl⟩ | ⟨q, -, hq, rfl⟩ | rfl | rfl | rfl | ⟨p, e, -, he, h | h⟩
  · obtain ⟨w, hw, h⟩ := psl_card_four hq
    exact ⟨2, w, hw, h, Or.inl rfl⟩
  · obtain ⟨w, hw, h⟩ := psl_card_eight hq
    exact ⟨3, w, hw, h, Or.inr (Or.inl rfl)⟩
  · exact ⟨3, 135, by decide, by norm_num, Or.inr (Or.inl rfl)⟩
  · exact ⟨3, 315, by decide, by norm_num, Or.inr (Or.inl rfl)⟩
  · exact ⟨3, 945, by decide, by norm_num, Or.inr (Or.inl rfl)⟩
  · obtain ⟨W, hW, hWe⟩ := l3_card_minus h.1
    obtain ⟨w, hw, hy⟩ := two_adic_of_mul he hW (h.2.trans hWe)
    exact ⟨5, w, hw, hy, Or.inr (Or.inr rfl)⟩
  · obtain ⟨W, hW, hWe⟩ := l3_card_plus h.1
    obtain ⟨w, hw, hy⟩ := two_adic_of_mul he hW (h.2.trans hWe)
    exact ⟨5, w, hw, hy, Or.inr (Or.inr rfl)⟩

theorem F618Ord.two_adic {y : ℕ} (h : F618Ord y) :
    ∃ a w, Odd w ∧ y = 2 ^ a * w ∧ (a = 2 ∨ a = 3 ∨ a = 5 ∨ (a = 6 ∧ y = 95040)) := by
  rcases h with h | rfl
  · obtain ⟨a, w, hw, hy, ha⟩ := h.two_adic
    exact ⟨a, w, hw, hy, by omega⟩
  · exact ⟨6, 1485, by decide, by norm_num, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩

theorem not_two_pow_dvd_of_odd {a w k : ℕ} (hw : Odd w) (hak : a < k) : ¬ 2 ^ k ∣ 2 ^ a * w := by
  intro h
  have h2 : 2 ^ a * 2 ^ (k - a) ∣ 2 ^ a * w := by
    rwa [← pow_add, Nat.add_sub_cancel' hak.le]
  have h3 : 2 ^ (k - a) ∣ w := Nat.dvd_of_mul_dvd_mul_left (by positivity) h2
  have h4 : 2 ∣ w := (dvd_pow_self 2 (by omega)).trans h3
  exact (Nat.not_even_iff_odd.mpr hw) (even_iff_two_dvd.mpr h4)

theorem F618Ord.not_two_pow_dvd {y k : ℕ} (hk : 7 ≤ k) (h : F618Ord y) : ¬ 2 ^ k ∣ y := by
  obtain ⟨a, w, hw, rfl, ha⟩ := h.two_adic
  exact not_two_pow_dvd_of_odd hw (by omega)

theorem F618OrdA.not_dvd_sixty_four {y : ℕ} (h : F618OrdA y) : ¬ 64 ∣ y := by
  obtain ⟨a, w, hw, rfl, ha⟩ := h.two_adic
  exact fun h64 => not_two_pow_dvd_of_odd (a := a) (k := 6) hw (by omega) (by simpa using h64)

end CFSG.Quasithin.Gold14610
