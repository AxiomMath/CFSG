module

public import CFSG.RankThree.GF2n.Stroth80.Sec84InputStmt
public import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

namespace CFSG.RankThree.GF2n.Stroth80

theorem psu6TwoPart_holds : PSU6TwoPartStatement := by
  intro f X _ _ hf hX
  obtain ⟨K, fK, finK, hK, ⟨e⟩⟩ := hX
  have hcard : Nat.card X =
      Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedSU 6 (2 ^ f) K)) :=
    Nat.card_congr e.toEquiv
  rw [hcard, CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU
    (K := K) (p := 2) (f := f) (n := 6) Nat.prime_two hf hK (by norm_num)]
  have h15 : 6 * (6 - 1) / 2 = 15 := by norm_num
  rw [h15]
  have h1q : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have hqe : Even ((2 ^ f : ℕ) : ℤ) := by
    rw [Int.even_coe_nat]
    exact Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hneg : Odd (-1 : ℤ) := odd_neg_one
  have hfac : ∀ i ∈ Finset.Icc 2 6, Odd ((((2 ^ f : ℕ) : ℤ) ^ i - (-1) ^ i).toNat) := by
    intro i hi
    have hi2 : 2 ≤ i := (Finset.mem_Icc.mp hi).1
    have hodd : Odd (((2 ^ f : ℕ) : ℤ) ^ i - (-1) ^ i) :=
      Even.sub_odd (hqe.pow_of_ne_zero (by omega)) hneg.pow
    have hnn := CFSG.Timmesfeld.ClassicalOrders.pow_sub_neg_one_pow_nonneg h1q i
    rw [← Int.odd_coe_nat, Int.toNat_of_nonneg hnn]
    exact hodd
  have hPodd : Odd (∏ i ∈ Finset.Icc 2 6, (((2 ^ f : ℕ) : ℤ) ^ i - (-1) ^ i).toNat) :=
    Finset.prod_induction (fun i : ℕ => (((2 ^ f : ℕ) : ℤ) ^ i - (-1) ^ i).toNat)
      (fun n : ℕ => Odd n) (fun a b ha hb => Odd.mul ha hb) odd_one hfac
  have hdvd : (2 ^ f + 1 : ℕ) ∣ (((2 ^ f : ℕ) : ℤ) ^ 3 - (-1) ^ 3).toNat := by
    rw [← Int.natCast_dvd_natCast,
      Int.toNat_of_nonneg (CFSG.Timmesfeld.ClassicalOrders.pow_sub_neg_one_pow_nonneg h1q 3)]
    have e1 : ((2 ^ f + 1 : ℕ) : ℤ) = ((2 ^ f : ℕ) : ℤ) + 1 := by
      rw [Nat.cast_add, Nat.cast_one]
    have e2 : ((2 ^ f : ℕ) : ℤ) ^ 3 - (-1) ^ 3 = ((2 ^ f : ℕ) : ℤ) ^ 3 + 1 ^ 3 := by
      ring
    rw [e1, e2]
    exact Odd.add_dvd_pow_add_pow _ _ (⟨1, by norm_num⟩ : Odd (3 : ℕ))
  have hgP : Nat.gcd 6 (2 ^ f + 1) ∣
      ∏ i ∈ Finset.Icc 2 6, (((2 ^ f : ℕ) : ℤ) ^ i - (-1) ^ i).toNat :=
    dvd_trans (Nat.gcd_dvd_right 6 (2 ^ f + 1))
      (dvd_trans hdvd (Finset.dvd_prod_of_mem
        (fun i : ℕ => (((2 ^ f : ℕ) : ℤ) ^ i - (-1) ^ i).toNat)
        (Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)))
  refine ⟨(∏ i ∈ Finset.Icc 2 6, (((2 ^ f : ℕ) : ℤ) ^ i - (-1) ^ i).toNat) /
    Nat.gcd 6 (2 ^ f + 1), ?_, ?_⟩
  · have hmul := Nat.mul_div_cancel' hgP
    rw [← hmul] at hPodd
    exact (Nat.odd_mul.mp hPodd).2
  · rw [Nat.mul_div_assoc _ hgP]

end CFSG.RankThree.GF2n.Stroth80
