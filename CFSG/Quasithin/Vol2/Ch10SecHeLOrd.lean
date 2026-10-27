module

public import CFSG.Quasithin.Vol2.Ch5Sec1Thm5114Orders
public import CFSG.Quasithin.Vol2.KGNatG2Order

public section

namespace CFSG.Quasithin.Vol2.Ch10.HeL

open Matrix CFSG.Assembly.LowTwoRank CFSG.Open CFSG.Blueprint CFSG.Quasithin

theorem not_two_pow_eleven_dvd : ¬ 2 ^ 11 ∣ (4030387200 : ℕ) := by norm_num

theorem ne_of_two_pow_eleven_dvd {x : ℕ} (h : 2 ^ 11 ∣ x) : x ≠ 4030387200 := fun he =>
  not_two_pow_eleven_dvd (he ▸ h)

theorem two_pow_eleven_dvd_pow {n k : ℕ} (h : 11 ≤ n * k) : 2 ^ 11 ∣ (2 ^ n) ^ k := by
  rw [← pow_mul]
  exact Nat.pow_dvd_pow 2 h

theorem sl3_poly_ne (n : ℕ) :
    (2 ^ n) ^ 3 * (((2 ^ n) ^ 3 - 1) * ((2 ^ n) ^ 2 - 1)) ≠ 4030387200 := by
  rcases Nat.lt_or_ge n 4 with hn | hn
  · interval_cases n <;> norm_num
  · exact ne_of_two_pow_eleven_dvd (Dvd.dvd.mul_right (two_pow_eleven_dvd_pow (by omega)) _)

theorem card_SL3_ne {F : Type} [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    Nat.card (SpecialLinearGroup (Fin 3) F) ≠ 4030387200 := by
  rw [H13.L34Orders.card_SL3, hF]
  exact sl3_poly_ne n

theorem card_statedSp_ne {F : Type} [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    Nat.card (CFSG.Assembly.LowTwoRank.StatedSp 2 F) ≠ 4030387200 := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hF]
  rcases Nat.lt_or_ge n 3 with hn | hn
  · rw [show Finset.Icc 1 2 = {1, 2} by rfl, Finset.prod_pair (by norm_num)]
    interval_cases n <;> norm_num
  · exact ne_of_two_pow_eleven_dvd
      (Dvd.dvd.mul_right (two_pow_eleven_dvd_pow (by norm_num; omega)) _)

theorem card_G2_derived_ne {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) : Nat.card ↥⁅quasithinG2 F, quasithinG2 F⁆ ≠ 4030387200 := by
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
    exact ne_of_two_pow_eleven_dvd (Dvd.dvd.mul_right (two_pow_eleven_dvd_pow (by omega)) _)

theorem gcd_two_two_pow_sub_one {n : ℕ} (hn : 1 ≤ n) : Nat.gcd 2 (2 ^ n - 1) = 1 := by
  obtain ⟨c, hc⟩ : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hm : (2 ^ n - 1) % 2 = 1 := by omega
  rw [Nat.gcd_rec, hm, Nat.gcd_one_left]

theorem ordA_one_ne (n : ℕ) : ordA 1 (2 ^ n) ≠ 4030387200 := by
  unfold ordA
  rw [show 1 * (1 + 1) / 2 = 1 by rfl, pow_one, show Finset.Icc 2 (1 + 1) = {2} by rfl,
    Finset.prod_singleton]
  rcases Nat.lt_or_ge n 11 with hn | hn
  · interval_cases n <;> decide
  · rw [show (1 + 1 : ℕ) = 2 from rfl, gcd_two_two_pow_sub_one (by omega), Nat.div_one]
    exact ne_of_two_pow_eleven_dvd (Dvd.dvd.mul_right (Nat.pow_dvd_pow 2 hn) _)

theorem card_SL2 {F : Type} [Field F] [Finite F] :
    Nat.card (SpecialLinearGroup (Fin 2) F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  have : Fintype F := Fintype.ofFinite F
  rw [Matrix.card_SL_field, Fin.prod_univ_two, ← Nat.card_eq_fintype_card]
  set q := Nat.card F with hq
  have hq1 : 1 ≤ q := Nat.card_pos
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  have e : q ^ 2 - q = q * (q - 1) := by
    rw [Nat.mul_sub, mul_one]
    ring_nf
  rw [e]
  rcases (show 0 < q - 1 ∨ q = 1 by omega) with h | h
  · rw [show (q ^ 2 - 1) * (q * (q - 1)) = q * (q ^ 2 - 1) * (q - 1) by ring]
    exact Nat.mul_div_cancel _ h
  · rw [h]
    simp

theorem card_SL2_ne {F : Type} [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ (2 * n)) :
    Nat.card (SpecialLinearGroup (Fin 2) F) ≠ 4030387200 := by
  rw [card_SL2, hF]
  rcases Nat.lt_or_ge n 6 with hn | hn
  · interval_cases n <;> norm_num
  · exact ne_of_two_pow_eleven_dvd (Dvd.dvd.mul_right (Nat.pow_dvd_pow 2 (by omega)) _)

theorem mul_two_pow_ne {N : ℕ} (hN : N < 4030387200) (k : ℕ) : 4030387200 * 2 ^ k ≠ N := by
  have := Nat.one_le_two_pow (n := k)
  omega

end CFSG.Quasithin.Vol2.Ch10.HeL
