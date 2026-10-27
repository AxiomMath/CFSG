module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree

public section

namespace CFSG.Quasithin.H13.L34Orders

open Matrix CFSG.Assembly.LowTwoRank

theorem sl3_poly_ne (n : ℕ) : (2 ^ n) ^ 3 * (((2 ^ n) ^ 3 - 1) * ((2 ^ n) ^ 2 - 1)) ≠ 20160 := by
  rcases Nat.lt_or_ge n 3 with hn | hn
  · interval_cases n <;> norm_num
  · have hq : 8 ≤ 2 ^ n := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h1 : 512 ≤ (2 ^ n) ^ 3 := by
      calc 512 = 8 ^ 3 := by norm_num
        _ ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_left hq 3
    have h2 : 63 ≤ (2 ^ n) ^ 2 - 1 := by
      have : 64 ≤ (2 ^ n) ^ 2 := by
        calc 64 = 8 ^ 2 := by norm_num
          _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left hq 2
      omega
    have h3 : 511 ≤ (2 ^ n) ^ 3 - 1 := by omega
    have : 512 * (511 * 63) ≤ (2 ^ n) ^ 3 * (((2 ^ n) ^ 3 - 1) * ((2 ^ n) ^ 2 - 1)) :=
      Nat.mul_le_mul h1 (Nat.mul_le_mul h3 h2)
    omega

theorem card_SL3 {F : Type} [Field F] [Finite F] :
    Nat.card (SpecialLinearGroup (Fin 3) F) =
      Nat.card F ^ 3 * ((Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1)) := by
  have : Fintype F := Fintype.ofFinite F
  rw [Matrix.card_SL_field, Fin.prod_univ_three, ← Nat.card_eq_fintype_card]
  set q := Nat.card F with hq
  have hq1 : 1 ≤ q := Nat.card_pos
  have e1 : q ^ 3 - q = q * (q ^ 2 - 1) := by
    rw [Nat.mul_sub, mul_one]; ring_nf
  have e2 : q ^ 3 - q ^ 2 = q ^ 2 * (q - 1) := by
    rw [Nat.mul_sub, mul_one]; ring_nf
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
  rw [e1, e2]
  rcases (show 0 < q - 1 ∨ q = 1 by omega) with h | h
  · rw [show (q ^ 3 - 1) * (q * (q ^ 2 - 1)) * (q ^ 2 * (q - 1)) =
        q ^ 3 * ((q ^ 3 - 1) * (q ^ 2 - 1)) * (q - 1) by ring]
    exact Nat.mul_div_cancel _ h
  · rw [h]; simp

theorem card_SL3_ne_20160 {F : Type} [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    Nat.card (SpecialLinearGroup (Fin 3) F) ≠ 20160 := by
  rw [card_SL3, hF]
  exact sl3_poly_ne n

theorem card_statedSp_ne_20160 {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) : Nat.card (StatedSp 2 F) ≠ 20160 := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hF]
  rw [show Finset.Icc 1 2 = {1, 2} by rfl, Finset.prod_pair (by norm_num)]
  rcases Nat.lt_or_ge n 3 with hn | hn
  · interval_cases n <;> norm_num
  · have hq : 8 ≤ 2 ^ n := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h1 : 4096 ≤ (2 ^ n) ^ (2 ^ 2) := by
      calc 4096 = 8 ^ 4 := by norm_num
        _ ≤ (2 ^ n) ^ (2 ^ 2) := Nat.pow_le_pow_left hq 4
    have h2 : 63 ≤ (2 ^ n) ^ (2 * 1) - 1 := by
      have : 64 ≤ (2 ^ n) ^ (2 * 1) := by
        calc 64 = 8 ^ 2 := by norm_num
          _ ≤ (2 ^ n) ^ (2 * 1) := Nat.pow_le_pow_left hq 2
      omega
    have h3 : 1 ≤ (2 ^ n) ^ (2 * 2) - 1 := by
      have : 2 ≤ (2 ^ n) ^ (2 * 2) := by
        calc 2 ≤ 8 ^ 4 := by norm_num
          _ ≤ (2 ^ n) ^ (2 * 2) := Nat.pow_le_pow_left hq 4
      omega
    have : 4096 * (63 * 1) ≤
        (2 ^ n) ^ (2 ^ 2) * (((2 ^ n) ^ (2 * 1) - 1) * ((2 ^ n) ^ (2 * 2) - 1)) :=
      Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
    omega

theorem card_statedSU_ne_20160 {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = (2 ^ n) ^ 2) : Nat.card (StatedSU 3 (2 ^ n) F) ≠ 20160 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.SectionRank.OddCover.card_statedSU_three hF]
  rcases Nat.lt_or_ge n 3 with hn | hn
  · interval_cases n <;> norm_num
  · have hq : 8 ≤ 2 ^ n := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h1 : 512 ≤ (2 ^ n) ^ 3 := by
      calc 512 = 8 ^ 3 := by norm_num
        _ ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_left hq 3
    have h2 : 63 ≤ (2 ^ n) ^ 2 - 1 := by
      have : 64 ≤ (2 ^ n) ^ 2 := by
        calc 64 = 8 ^ 2 := by norm_num
          _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left hq 2
      omega
    have h3 : 1 ≤ (2 ^ n) ^ 3 + 1 := by omega
    have : 512 * 63 * 1 ≤ (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
    omega

theorem card_SL4_two : Nat.card (SpecialLinearGroup (Fin 4) (ZMod 2)) = 20160 := by
  rw [Matrix.card_SL_field]
  simp [Fin.prod_univ_four]

theorem card_SL5_two : Nat.card (SpecialLinearGroup (Fin 5) (ZMod 2)) = 9999360 := by
  rw [Matrix.card_SL_field]
  simp [Fin.prod_univ_five]

theorem card_alt (n : ℕ) (hn : 2 ≤ n) :
    Nat.card (alternatingGroup (Fin n)) = n.factorial / 2 := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]

end CFSG.Quasithin.H13.L34Orders
