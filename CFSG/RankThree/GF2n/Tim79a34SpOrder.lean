module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.Open.StatedDefs
public import Mathlib.FieldTheory.Finite.GaloisField

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.Open

theorem card_statedSp_gf2 (n : ℕ) :
    Nat.card ↥(StatedSp n (GaloisField 2 1)) =
      2 ^ (n ^ 2) * ∏ j ∈ Finset.Icc 1 n, (2 ^ (2 * j) - 1) := by
  have hF2 : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 one_ne_zero, pow_one]
  rw [LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hF2]

theorem card_statedSp_gf2_pos (n : ℕ) : 0 < Nat.card ↥(StatedSp n (GaloisField 2 1)) := by
  rw [card_statedSp_gf2]
  refine Nat.mul_pos (by positivity) (Finset.prod_pos fun j hj => ?_)
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have : 1 < 2 ^ (2 * j) := Nat.one_lt_two_pow (by omega)
  omega

theorem card_statedSp_gf2_succ (n : ℕ) :
    Nat.card ↥(StatedSp (n + 1) (GaloisField 2 1)) =
      Nat.card ↥(StatedSp n (GaloisField 2 1)) * (2 ^ (2 * n + 1) * (2 ^ (2 * (n + 1)) - 1)) := by
  rw [card_statedSp_gf2, card_statedSp_gf2, Finset.prod_Icc_succ_top (by omega)]
  have h : (n + 1) ^ 2 = n ^ 2 + (2 * n + 1) := by ring
  rw [h, pow_add]
  ring

theorem card_statedSp_gf2_strictMono :
    StrictMono fun n : ℕ => Nat.card ↥(StatedSp n (GaloisField 2 1)) := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  show Nat.card ↥(StatedSp n (GaloisField 2 1)) < Nat.card ↥(StatedSp (n + 1) (GaloisField 2 1))
  rw [card_statedSp_gf2_succ]
  have hpos := card_statedSp_gf2_pos n
  have h1 : 2 ≤ 2 ^ (2 * n + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 3 ≤ 2 ^ (2 * (n + 1)) - 1 := by
    have : 4 ≤ 2 ^ (2 * (n + 1)) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (2 * (n + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h3 : 1 < 2 ^ (2 * n + 1) * (2 ^ (2 * (n + 1)) - 1) := by
    calc 1 < 2 * 3 := by norm_num
      _ ≤ _ := Nat.mul_le_mul h1 h2
  calc Nat.card ↥(StatedSp n (GaloisField 2 1))
      = Nat.card ↥(StatedSp n (GaloisField 2 1)) * 1 := (mul_one _).symm
    _ < _ := Nat.mul_lt_mul_of_pos_left h3 hpos

theorem statedSp_gf2_rank_eq {n m : ℕ}
    (e : ↥(StatedSp n (GaloisField 2 1)) ≃* ↥(StatedSp m (GaloisField 2 1))) : n = m :=
  card_statedSp_gf2_strictMono.injective (Nat.card_congr e.toEquiv)

end CFSG.RankThree.GF2n.Tim79a
