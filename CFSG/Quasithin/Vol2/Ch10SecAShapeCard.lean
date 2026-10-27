module

public import CFSG.Quasithin.Vol2.Ch10SecAShape
public import CFSG.Quasithin.Vol2.Ch10SecA1012Five

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Assembly.LowTwoRank

theorem card_statedSL (d : ℕ) (F : Type) [Field F] :
    Nat.card ↥(StatedSL d F) = Nat.card (Matrix.SpecialLinearGroup (Fin d) F) :=
  CFSG.Open.StatedAPI.card_statedSL d F

theorem card_SL_three_pow {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 3) K) =
      2 ^ (3 * n) * ((2 ^ (3 * n) - 1) * (2 ^ (2 * n) - 1)) := by
  have := Fintype.ofFinite K
  rw [Matrix.card_SL_field, Fin.prod_univ_three]
  simp only [Fin.val_zero, pow_zero, Fin.val_one, pow_one, Fin.val_two]
  rw [← Nat.card_eq_fintype_card, hK]
  set q := 2 ^ n with hq
  have hq1 : 1 ≤ q := Nat.one_le_two_pow
  have hpos : 0 < q - 1 := by
    have : 2 ≤ q := by
      have h := Finite.one_lt_card (α := K)
      rw [hK] at h
      omega
    omega
  have h1 : q ^ 3 - q = q * (q ^ 2 - 1) := by
    rw [Nat.mul_sub_one, show q * q ^ 2 = q ^ 3 by ring]
  have h2 : q ^ 3 - q ^ 2 = q ^ 2 * (q - 1) := by
    rw [Nat.mul_sub_one, show q ^ 2 * q = q ^ 3 by ring]
  rw [h1, h2, show (q ^ 3 - 1) * (q * (q ^ 2 - 1)) * (q ^ 2 * (q - 1)) =
      q ^ 3 * ((q ^ 3 - 1) * (q ^ 2 - 1)) * (q - 1) by ring, Nat.mul_div_cancel _ hpos, hq,
    ← pow_mul, ← pow_mul, mul_comm n 3, mul_comm n 2]

theorem card_Sp4_pow {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    Nat.card ↥(StatedSp 2 K) = 2 ^ (4 * n) * ((2 ^ (2 * n) - 1) * (2 ^ (4 * n) - 1)) := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp]
  have hI : Finset.Icc 1 2 = {1, 2} := by decide
  rw [hI, Finset.prod_pair (by norm_num), hK, ← pow_mul, ← pow_mul, ← pow_mul]
  norm_num [mul_comm n]

theorem card_SL_four_of_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 4) K) = 20160 := by
  have := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  rw [Matrix.card_SL_field, hK']
  simp [Fin.prod_univ_four]

theorem card_SL_five_of_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 5) K) = 9999360 := by
  have := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  rw [Matrix.card_SL_field, hK']
  simp [Fin.prod_univ_five]

theorem card_alt (n : ℕ) (hn : 2 ≤ n) :
    Nat.card ↥(alternatingGroup (Fin n)) = n.factorial / 2 := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]

theorem isSimpleGroup_alt {n : ℕ} (hn : 5 ≤ n) : IsSimpleGroup ↥(alternatingGroup (Fin n)) :=
  alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hn)

theorem isSimpleGroup_statedSL_two {n : ℕ} (hn : 3 ≤ n) :
    IsSimpleGroup ↥(StatedSL n (ZMod 2)) := by
  have := isSimpleGroup_SL_two hn
  exact (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n (ZMod 2)).symm.isSimpleGroup

theorem odd_two_pow_sub_one {k : ℕ} (hk : 1 ≤ k) : Odd (2 ^ k - 1) :=
  Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one

theorem three_dvd_two_pow_two_mul_sub_one (n : ℕ) : 3 ∣ 2 ^ (2 * n) - 1 := by
  rw [pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num]
  simpa using Nat.sub_one_dvd_pow_sub_one 4 n

theorem ne_four_pow_sub_one_of_lt {a b c : ℕ} (hb : b < 2 ^ c) (hc : c < 2 * a) :
    b ≠ 4 ^ a - 1 := by
  have h4 : 4 ^ a = 2 ^ (2 * a) := by rw [pow_mul]; norm_num
  have h1 : 2 ^ (c + 1) ≤ 2 ^ (2 * a) := Nat.pow_le_pow_right (by norm_num) hc
  have h2 : 1 ≤ 2 ^ c := Nat.one_le_two_pow
  rw [pow_succ] at h1
  omega

theorem mul_two_pow_sub_one_lt (u v : ℕ) : (2 ^ u - 1) * (2 ^ v - 1) < 2 ^ (u + v) := by
  rw [pow_add]
  exact mul_lt_mul'' (Nat.sub_lt Nat.one_le_two_pow one_pos)
    (Nat.sub_lt Nat.one_le_two_pow one_pos) (Nat.zero_le _) (Nat.zero_le _)

theorem not_shapeCard_SL_three {n : ℕ} (hn : 2 ≤ n) :
    ¬ ShapeCard (2 ^ (3 * n) * ((2 ^ (3 * n) - 1) * (2 ^ (2 * n) - 1))) := by
  refine not_shapeCard_of ((odd_two_pow_sub_one (by omega)).mul (odd_two_pow_sub_one (by omega)))
    (Dvd.dvd.mul_left (three_dvd_two_pow_two_mul_sub_one n) _) (fun _ => ?_) (fun h => by omega)
  exact ne_four_pow_sub_one_of_lt (mul_two_pow_sub_one_lt _ _) (by omega)

theorem not_shapeCard_Sp4 {n : ℕ} (hn : 1 ≤ n) :
    ¬ ShapeCard (2 ^ (4 * n) * ((2 ^ (2 * n) - 1) * (2 ^ (4 * n) - 1))) := by
  refine not_shapeCard_of ((odd_two_pow_sub_one (by omega)).mul (odd_two_pow_sub_one (by omega)))
    (Dvd.dvd.mul_right (three_dvd_two_pow_two_mul_sub_one n) _) (fun _ => ?_) (fun h => by omega)
  exact ne_four_pow_sub_one_of_lt (mul_two_pow_sub_one_lt _ _) (by omega)

theorem not_shapeCard_num {N a b : ℕ} (hN : N = 2 ^ a * b) (hb : Odd b) (h3 : 3 ∣ b)
    (hne : b ≠ 4 ^ a - 1) (h168 : a ≠ 3) : ¬ ShapeCard N :=
  hN ▸ not_shapeCard_of hb h3 (fun _ => hne) (fun h => absurd h h168)

theorem not_shapeCard_six : ¬ ShapeCard 6 :=
  not_shapeCard_of (a := 1) (b := 3) (by decide) (by decide) (by omega) (by omega)

theorem not_shapeCard_360 : ¬ ShapeCard 360 :=
  not_shapeCard_of (a := 3) (b := 45) (by decide) (by decide) (by decide) (by decide)

theorem not_shapeCard_2520 : ¬ ShapeCard 2520 :=
  not_shapeCard_of (a := 3) (b := 315) (by decide) (by decide) (by decide) (by decide)

theorem not_shapeCard_6048 : ¬ ShapeCard 6048 :=
  not_shapeCard_num (a := 5) (b := 189) (by norm_num) (by decide) (by decide) (by decide)
    (by decide)

theorem not_shapeCard_20160 : ¬ ShapeCard 20160 :=
  not_shapeCard_num (a := 6) (b := 315) (by norm_num) (by decide) (by decide) (by decide)
    (by decide)

theorem not_shapeCard_604800 : ¬ ShapeCard 604800 :=
  not_shapeCard_num (a := 7) (b := 4725) (by norm_num) (by decide) (by decide) (by decide)
    (by decide)

theorem not_shapeCard_9999360 : ¬ ShapeCard 9999360 :=
  not_shapeCard_num (a := 10) (b := 9765) (by norm_num) (by decide) (by decide) (by decide)
    (by decide)

theorem not_shapeCard_244823040 : ¬ ShapeCard 244823040 :=
  not_shapeCard_num (a := 10) (b := 239085) (by norm_num) (by decide) (by decide) (by decide)
    (by decide)

end CFSG.Quasithin.Vol2.Ch10.SecA
