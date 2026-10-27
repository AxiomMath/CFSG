module

public import CFSG.Quasithin.Vol2.Ch5Sec1Thm5114Orders
public import CFSG.Quasithin.EmptyFaithful.T1515dB

public section

namespace CFSG.Quasithin.H13.J1Orders

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank Matrix

theorem ordA_one_two_pow_ne_j1 (n : ℕ) : ordA 1 (2 ^ n) ≠ 175560 := by
  unfold ordA
  rw [show 1 * (1 + 1) / 2 = 1 by rfl, pow_one, show Finset.Icc 2 (1 + 1) = {2} by rfl,
    Finset.prod_singleton]
  rcases Nat.lt_or_ge n 6 with hn | hn
  · interval_cases n <;> decide
  · have hq : 64 ≤ 2 ^ n :=
      calc 64 = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have hodd : Nat.gcd (1 + 1) (2 ^ n - 1) = 1 := by
      have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
      have h3 : (2 ^ n - 1) % 2 = 1 := by omega
      rw [show (1 + 1 : ℕ) = 2 by rfl]
      exact Nat.coprime_two_left.mpr (Nat.odd_iff.mpr h3)
    rw [hodd, Nat.div_one]
    have h2 : 4095 ≤ (2 ^ n) ^ 2 - 1 := by
      have : 4096 ≤ (2 ^ n) ^ 2 :=
        calc 4096 = 64 ^ 2 := by norm_num
          _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left hq 2
      omega
    have : 64 * 4095 ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) := Nat.mul_le_mul hq h2
    omega

theorem ordA_two_two_pow_ne_j1 (n : ℕ) : ordA 2 (2 ^ n) ≠ 175560 := by
  unfold ordA
  rw [show 2 * (2 + 1) / 2 = 3 by rfl, show Finset.Icc 2 (2 + 1) = {2, 3} by rfl,
    Finset.prod_pair (by norm_num)]
  rcases Nat.lt_or_ge n 3 with hn | hn
  · interval_cases n <;> decide
  · have hq : 8 ≤ 2 ^ n :=
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have hg : Nat.gcd (2 + 1) (2 ^ n - 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
    have hg0 : 0 < Nat.gcd (2 + 1) (2 ^ n - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have h1 : 512 ≤ (2 ^ n) ^ 3 :=
      calc 512 = 8 ^ 3 := by norm_num
        _ ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_left hq 3
    have h2 : 63 ≤ (2 ^ n) ^ 2 - 1 := by
      have : 64 ≤ (2 ^ n) ^ 2 :=
        calc 64 = 8 ^ 2 := by norm_num
          _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left hq 2
      omega
    have h3 : 511 ≤ (2 ^ n) ^ 3 - 1 := by omega
    have hX : 512 * (63 * 511) ≤ (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) :=
      Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
    have h4 : (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) / 3 ≤
        (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) / Nat.gcd (2 + 1) (2 ^ n - 1) :=
      Nat.div_le_div_left hg hg0
    have h5 : 175560 + 1 ≤ (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) / 3 :=
      (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)
    exact (Nat.lt_of_lt_of_le (Nat.lt_of_succ_le h5) h4).ne'

theorem sl3_poly_ne_j1 (n : ℕ) :
    (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) ≠ 175560 := by
  rcases Nat.lt_or_ge n 3 with hn | hn
  · interval_cases n <;> norm_num
  · have hq : 8 ≤ 2 ^ n :=
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h1 : 512 ≤ (2 ^ n) ^ 3 :=
      calc 512 = 8 ^ 3 := by norm_num
        _ ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_left hq 3
    have h2 : 63 ≤ (2 ^ n) ^ 2 - 1 := by
      have : 64 ≤ (2 ^ n) ^ 2 :=
        calc 64 = 8 ^ 2 := by norm_num
          _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left hq 2
      omega
    have h3 : 511 ≤ (2 ^ n) ^ 3 - 1 := by omega
    have : 512 * (63 * 511) ≤ (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) :=
      Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
    omega

theorem card_statedSL3_ne_j1 {F : Type} [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    Nat.card ↥(Assembly.LowTwoRank.StatedSL 3 F) ≠ 175560 := by
  rw [card_statedSL_three1527d, hF]
  exact sl3_poly_ne_j1 n

theorem card_SL3_ne_j1 {F : Type} [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    Nat.card (SpecialLinearGroup (Fin 3) F) ≠ 175560 := by
  rw [L34Orders.card_SL3, hF]
  rcases Nat.lt_or_ge n 3 with hn | hn
  · interval_cases n <;> norm_num
  · have hq : 8 ≤ 2 ^ n :=
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h1 : 512 ≤ (2 ^ n) ^ 3 :=
      calc 512 = 8 ^ 3 := by norm_num
        _ ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_left hq 3
    have h2 : 63 ≤ (2 ^ n) ^ 2 - 1 := by
      have : 64 ≤ (2 ^ n) ^ 2 :=
        calc 64 = 8 ^ 2 := by norm_num
          _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left hq 2
      omega
    have h3 : 511 ≤ (2 ^ n) ^ 3 - 1 := by omega
    have : 512 * (511 * 63) ≤ (2 ^ n) ^ 3 * (((2 ^ n) ^ 3 - 1) * ((2 ^ n) ^ 2 - 1)) :=
      Nat.mul_le_mul h1 (Nat.mul_le_mul h3 h2)
    omega

theorem card_statedSp_ne_j1 {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) : Nat.card (Assembly.LowTwoRank.StatedSp 2 F) ≠ 175560 := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hF]
  rw [show Finset.Icc 1 2 = {1, 2} by rfl, Finset.prod_pair (by norm_num)]
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n <;> norm_num
  · have hq : 4 ≤ 2 ^ n :=
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h1 : 256 ≤ (2 ^ n) ^ (2 ^ 2) :=
      calc 256 = 4 ^ 4 := by norm_num
        _ ≤ (2 ^ n) ^ (2 ^ 2) := Nat.pow_le_pow_left hq 4
    have h2 : 15 ≤ (2 ^ n) ^ (2 * 1) - 1 := by
      have : 16 ≤ (2 ^ n) ^ (2 * 1) :=
        calc 16 = 4 ^ 2 := by norm_num
          _ ≤ (2 ^ n) ^ (2 * 1) := Nat.pow_le_pow_left hq 2
      omega
    have h3 : 255 ≤ (2 ^ n) ^ (2 * 2) - 1 := by
      have : 256 ≤ (2 ^ n) ^ (2 * 2) :=
        calc 256 = 4 ^ 4 := by norm_num
          _ ≤ (2 ^ n) ^ (2 * 2) := Nat.pow_le_pow_left hq 4
      omega
    have : 256 * (15 * 255) ≤
        (2 ^ n) ^ (2 ^ 2) * (((2 ^ n) ^ (2 * 1) - 1) * ((2 ^ n) ^ (2 * 2) - 1)) :=
      Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
    omega

theorem card_statedSU_ne_j1 {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = (2 ^ n) ^ 2) :
    Nat.card (Assembly.LowTwoRank.StatedSU 3 (2 ^ n) F) ≠ 175560 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.SectionRank.OddCover.card_statedSU_three hF]
  rcases Nat.lt_or_ge n 3 with hn | hn
  · interval_cases n <;> norm_num
  · have hq : 8 ≤ 2 ^ n :=
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h1 : 512 ≤ (2 ^ n) ^ 3 :=
      calc 512 = 8 ^ 3 := by norm_num
        _ ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_left hq 3
    have h2 : 63 ≤ (2 ^ n) ^ 2 - 1 := by
      have : 64 ≤ (2 ^ n) ^ 2 :=
        calc 64 = 8 ^ 2 := by norm_num
          _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left hq 2
      omega
    have h3 : 513 ≤ (2 ^ n) ^ 3 + 1 := by omega
    have : 512 * 63 * 513 ≤ (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
    omega

theorem card_G2_derived_ne_j1 {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) : Nat.card ↥⁅quasithinG2 F, quasithinG2 F⁆ ≠ 175560 := by
  rcases n with _ | _ | n
  · exfalso
    have := Finite.one_lt_card (α := F)
    rw [hF] at this
    norm_num at this
  · have : CharP F 2 := Vol2.KGNat.charP_two_of_card (n := 1) one_ne_zero hF
    have hG : Nat.card ↥(quasithinG2 F) = 12096 := by
      rw [CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup,
        Vol2.KGNat.card_cayleyGroup, hF]
      norm_num
    have : Finite ↥(quasithinG2 F) := Nat.finite_of_card_ne_zero (by rw [hG]; norm_num)
    have hle := Subgroup.card_le_of_le (Subgroup.commutator_le_self (quasithinG2 F))
    omega
  · rw [Vol2.KGNat.factG2DerivedOrder_holds F (n + 2) (by omega) hF]
    have hq : 4 ≤ 2 ^ (n + 2) :=
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (n + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    generalize 2 ^ (n + 2) = q at hq ⊢
    have h6 : 4096 ≤ q ^ 6 :=
      calc 4096 = 4 ^ 6 := by norm_num
        _ ≤ q ^ 6 := Nat.pow_le_pow_left hq 6
    have h2 : 16 ≤ q ^ 2 :=
      calc 16 = 4 ^ 2 := by norm_num
        _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
    have : 4096 * (4095 * 15) ≤ q ^ 6 * ((q ^ 6 - 1) * (q ^ 2 - 1)) :=
      Nat.mul_le_mul h6 (Nat.mul_le_mul (by omega) (by omega))
    omega

theorem mul_two_pow_ne_j1 (k : ℕ) :
    175560 * 2 ^ k ≠ 2520 ∧ 175560 * 2 ^ k ≠ 20160 ∧ 175560 * 2 ^ k ≠ 9999360 ∧
      175560 * 2 ^ k ≠ 190080 := by
  have h1 := Nat.one_le_two_pow (n := k)
  refine ⟨by omega, by omega, fun h => ?_, fun h => ?_⟩
  · have hk : k < 6 := by
      by_contra hk
      have : 2 ^ 6 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases k <;> omega
  · have hk : k < 1 := by
      by_contra hk
      have : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases k
    omega

end CFSG.Quasithin.H13.J1Orders
