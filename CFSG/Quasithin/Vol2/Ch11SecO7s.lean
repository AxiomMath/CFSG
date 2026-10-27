module

public import CFSG.Quasithin.Vol2.Ch11SecO7r
public import CFSG.Quasithin.Vol2.Ch11SecO7o

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE.C10KH

open CFSG.Open CFSG.Blueprint

theorem six_le_of_list2 {X : Type} [Group X] {n : ℕ} (hn : 2 ≤ n) {A : ℕ}
    (hA : (A = 3 * n ∧ (IsSL3 (2 ^ n) X ∨ IsPSL 3 2 n X)) ∨ A = 4 * n ∨ A = 6 * n ∨ A = 12 * n) :
    6 ≤ A := by
  rcases hA with ⟨rfl, -⟩ | rfl | rfl | rfl <;> omega


variable {X : Type} [Group X] {n : ℕ}

theorem list2_ge (hn : 2 ≤ n) (h : List11_1_1Two X n) : 20160 ≤ Nat.card X := by
  obtain ⟨A, u, ⟨hN, -, -, hu, -⟩, hA⟩ := list2_profile hn h
  rw [hN]
  calc 20160 = 2 ^ 6 * 315 := by norm_num
    _ ≤ 2 ^ A * u := Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (six_le_of_list2 hn hA)) hu

theorem list2_three_dvd (hn : 2 ≤ n) (h : List11_1_1Two X n) : 3 ∣ Nat.card X := by
  obtain ⟨A, u, ⟨hN, -, h3, -⟩, -⟩ := list2_profile hn h
  exact hN ▸ Dvd.dvd.mul_left h3 _

theorem list2_n_eq_two (hn : 2 ≤ n) (h : List11_1_1Two X n) (h8 : ¬ 2 ^ 8 ∣ Nat.card X) :
    n = 2 := by
  obtain ⟨A, u, ⟨hN, -⟩, hA⟩ := list2_profile hn h
  have hA7 : A ≤ 7 := by
    by_contra h'
    exact h8 (hN ▸ (Nat.pow_dvd_pow 2 (by omega)).mul_right u)
  rcases hA with ⟨rfl, -⟩ | rfl | rfl | rfl <;> omega

theorem list2_two_adic (hn : 2 ≤ n) (h : List11_1_1Two X n) {A' u' : ℕ} (hu' : Odd u')
    (hc : Nat.card X = 2 ^ A' * u') : A' = 3 * n ∨ A' = 4 * n ∨ A' = 6 * n ∨ A' = 12 * n := by
  obtain ⟨A, u, ⟨hN, hu, -⟩, hA⟩ := list2_profile hn h
  obtain rfl : A = A' := SecA.eq_of_two_pow_mul_odd hu hu' (hN.symm.trans hc)
  rcases hA with ⟨h3, -⟩ | h4 | h6 | h12
  · exact Or.inl h3
  · exact Or.inr (Or.inl h4)
  · exact Or.inr (Or.inr (Or.inl h6))
  · exact Or.inr (Or.inr (Or.inr h12))

theorem list2_ne_l2two (hn : 2 ≤ n) (h : List11_1_1Two X n) (m : ℕ) :
    Nat.card X ≠ 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
  obtain ⟨A, u, ⟨hN, hu, -, -, hlt⟩, -⟩ := list2_profile hn h
  exact fun hc => l2two_ne_profile hu hlt m (hc.symm.trans hN)

theorem list2_ne_artin (hn : 2 ≤ n) (h : List11_1_1Two X n) {c q : ℕ} (hc : Odd c) (hq : Odd q)
    (hq3 : 3 ≤ q) : Nat.card X * 2 ≠ c * (q * (q ^ 2 - 1)) := by
  obtain ⟨A, u, ⟨hN, hu, -, -, hlt⟩, hA⟩ := list2_profile hn h
  rw [hN]
  exact ne_of_artin (by have := six_le_of_list2 hn hA; omega) hu hlt hc hq hq3

theorem list2_20160 (hn : 2 ≤ n) (h : List11_1_1Two X n) (hc : Nat.card X = 20160) :
    IsPSL 3 2 2 X := by
  obtain ⟨A, u, ⟨hN, hu, -⟩, hA⟩ := list2_profile hn h
  have h1 : 2 ^ A * u = 2 ^ 6 * 315 := hN.symm.trans (hc.trans (by norm_num))
  have hA6 : A = 6 := SecA.eq_of_two_pow_mul_odd hu ⟨157, rfl⟩ h1
  rcases hA with ⟨h3, hX⟩ | h4 | h6 | h12
  · obtain rfl : n = 2 := by omega
    rcases hX with ⟨K, _, _, hK, ⟨e⟩⟩ | hX
    · exfalso
      have : Nat.card X = 60480 := by
        rw [Nat.card_congr (e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL
          3 K).symm).toEquiv, CFSG.OrderReductions.LinearOrders.card_specialLinear K 3
          (by norm_num), hK]
        decide
      omega
    · exact hX
  all_goals omega

end CFSG.Quasithin.Vol2.Ch11.SecE.C10KH
