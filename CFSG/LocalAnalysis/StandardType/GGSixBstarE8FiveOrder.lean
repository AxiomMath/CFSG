module

public import CFSG.RankThree.PartOne.KE.CTCasesCycloGlue
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace NoOffE8Five

section Order


theorem five_sq_eq_neg_one {q : ℕ} (h5 : 5 ∣ q * q + 1) : (q : ZMod 5) ^ 2 = -1 := by
  have h5z : ((q * q + 1 : ℕ) : ZMod 5) = 0 := (ZMod.natCast_eq_zero_iff (q * q + 1) 5).2 h5
  push_cast at h5z
  have : (q : ZMod 5) ^ 2 + 1 = 0 := by simpa [pow_two] using h5z
  exact eq_neg_iff_add_eq_zero.2 this

theorem five_not_dvd_of_dvd_sq_add_one {q : ℕ} (h5 : 5 ∣ q * q + 1) : ¬ 5 ∣ q := by
  intro h
  have hq0 : (q : ZMod 5) = 0 := (ZMod.natCast_eq_zero_iff q 5).2 h
  have h := five_sq_eq_neg_one h5
  rw [hq0] at h
  exact absurd h (by decide)

theorem orderOf_five_of_dvd_sq_add_one {q : ℕ} (h5 : 5 ∣ q * q + 1) :
    orderOf (q : ZMod 5) = 4 := by
  have hqm1 := five_sq_eq_neg_one h5
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hnot : ¬ (q : ZMod 5) ^ (2 : ℕ) ^ (1 : ℕ) = 1 := by
    rw [pow_one, hqm1]
    decide
  have hfin : (q : ZMod 5) ^ (2 : ℕ) ^ (1 + 1) = 1 := by
    rw [show (2 : ℕ) ^ (1 + 1) = 4 by norm_num]
    calc (q : ZMod 5) ^ 4 = ((q : ZMod 5) ^ 2) ^ 2 := by ring
      _ = (-1 : ZMod 5) ^ 2 := by rw [hqm1]
      _ = 1 := by norm_num
  have h := orderOf_eq_prime_pow (x := (q : ZMod 5)) (p := 2) (n := 1) hnot hfin
  norm_num at h
  exact h

theorem ordProj_five_pow_four_mul_sub_one {q n : ℕ} (hq : 2 ≤ q) (hQ : 5 ∣ q ^ 4 - 1)
    (hQ5 : ¬ 5 ∣ q ^ 4) (hn : n ≠ 0) :
    ordProj[5] (q ^ (4 * n) - 1) = ordProj[5] (q ^ 4 - 1) * ordProj[5] n := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hQ1 : 1 < q ^ 4 := Nat.one_lt_pow (by norm_num) (by omega)
  have hlift := padicValNat.pow_sub_pow (x := q ^ 4) (y := 1) (p := 5) (by decide : Odd 5)
    hQ1 hQ hQ5 hn
  rw [one_pow, ← pow_mul] at hlift
  rw [Nat.factorization_def (q ^ (4 * n) - 1) (by norm_num : Nat.Prime 5),
      Nat.factorization_def (q ^ 4 - 1) (by norm_num : Nat.Prime 5),
      Nat.factorization_def n (by norm_num : Nat.Prime 5), hlift, pow_add]

theorem ordProj_five_four_sub_one_eq_sq_add_one {q : ℕ} (hq : 2 ≤ q) (h5 : 5 ∣ q * q + 1) :
    ordProj[5] (q ^ 4 - 1) = ordProj[5] (q * q + 1) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hq2le : 1 ≤ q ^ 2 := by
    have : 1 < q ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  have h52 : ¬ 5 ∣ q ^ 2 - 1 := by
    intro h
    have hsum : 5 ∣ q ^ 2 + 1 := by simpa [pow_two] using h5
    have h2 : 5 ∣ 2 := by
      have hsub : 5 ∣ q ^ 2 + 1 - (q ^ 2 - 1) := Nat.dvd_sub hsum h
      rwa [show q ^ 2 + 1 - (q ^ 2 - 1) = 2 by omega] at hsub
    exact absurd h2 (by norm_num)
  have hq2nz : q ^ 2 - 1 ≠ 0 := by
    have : 1 < q ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  have hq21nz : q ^ 2 + 1 ≠ 0 := by
    have : 0 < q ^ 2 + 1 := by positivity
    omega
  have hfac : q ^ 4 - 1 = (q ^ 2 - 1) * (q ^ 2 + 1) := by
    rw [show q ^ 4 = (q ^ 2) ^ 2 by ring]
    have h := sq_tsub_sq (q ^ 2) 1
    rw [one_pow, mul_comm] at h
    exact h
  rw [hfac, Nat.ordProj_mul 5 hq2nz hq21nz,
    CFSG.RankThree.PartOne.KE.CTE6.ordProj_eq_one_of_not_dvd h52, one_mul, pow_two]

theorem five_factors_prod {q : ℕ} (hq : 2 ≤ q) (h5 : 5 ∣ q * q + 1) :
    (([2, 8, 12, 14, 18, 20, 24, 30] : List ℕ).map fun d => ordProj[5] (q ^ d - 1)).prod =
      5 ^ (4 * (q * q + 1).factorization 5 + 1) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hpq : ¬ 5 ∣ q := five_not_dvd_of_dvd_sq_add_one h5
  have hq4le : 1 ≤ q ^ 4 := by
    have : 1 < q ^ 4 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  have hQ : 5 ∣ q ^ 4 - 1 := by
    rw [← ZMod.natCast_eq_zero_iff (q ^ 4 - 1) 5, Nat.cast_sub hq4le,
        Nat.cast_pow, Nat.cast_one]
    rw [show (q : ZMod 5) ^ 4 = ((q : ZMod 5) ^ 2) ^ 2 by ring, five_sq_eq_neg_one h5]
    norm_num
  have hQ5 : ¬ 5 ∣ q ^ 4 :=
    fun h => hpq ((by norm_num : Nat.Prime 5).dvd_of_dvd_pow h)
  have hone_of_not_four_dvd : ∀ d : ℕ, ¬ 4 ∣ d → ordProj[5] (q ^ d - 1) = 1 := by
    intro d hd
    exact CFSG.RankThree.PartOne.KE.CTE6.ordProj_eq_one_of_not_dvd
      (fun h => hd ((CFSG.RankThree.PartOne.KE.CTE6.dvd_pow_sub_one_iff (by omega)
        (orderOf_five_of_dvd_sq_add_one h5)).1 h))
  have h2 : ordProj[5] (q ^ 2 - 1) = 1 := hone_of_not_four_dvd 2 (by norm_num)
  have h8 : ordProj[5] (q ^ 8 - 1) = ordProj[5] (q ^ 4 - 1) := by
    have h := ordProj_five_pow_four_mul_sub_one (q := q) (n := 2) hq hQ hQ5 (by norm_num)
    rw [show 4 * 2 = 8 by norm_num] at h
    rw [h, CFSG.RankThree.PartOne.KE.CTE6.ordProj_eq_one_of_not_dvd (by norm_num : ¬ 5 ∣ 2),
      mul_one]
  have h12 : ordProj[5] (q ^ 12 - 1) = ordProj[5] (q ^ 4 - 1) := by
    have h := ordProj_five_pow_four_mul_sub_one (q := q) (n := 3) hq hQ hQ5 (by norm_num)
    rw [show 4 * 3 = 12 by norm_num] at h
    rw [h, CFSG.RankThree.PartOne.KE.CTE6.ordProj_eq_one_of_not_dvd (by norm_num : ¬ 5 ∣ 3),
      mul_one]
  have h14 : ordProj[5] (q ^ 14 - 1) = 1 := hone_of_not_four_dvd 14 (by norm_num)
  have h18 : ordProj[5] (q ^ 18 - 1) = 1 := hone_of_not_four_dvd 18 (by norm_num)
  have h20 : ordProj[5] (q ^ 20 - 1) = ordProj[5] (q ^ 4 - 1) * 5 := by
    have h := ordProj_five_pow_four_mul_sub_one (q := q) (n := 5) hq hQ hQ5 (by norm_num)
    rw [show 4 * 5 = 20 by norm_num] at h
    rw [h, Nat.Prime.factorization_self (p := 5) (by norm_num : Nat.Prime 5), pow_one]
  have h24 : ordProj[5] (q ^ 24 - 1) = ordProj[5] (q ^ 4 - 1) := by
    have h := ordProj_five_pow_four_mul_sub_one (q := q) (n := 6) hq hQ hQ5 (by norm_num)
    rw [show 4 * 6 = 24 by norm_num] at h
    rw [h, CFSG.RankThree.PartOne.KE.CTE6.ordProj_eq_one_of_not_dvd (by norm_num : ¬ 5 ∣ 6),
      mul_one]
  have h30 : ordProj[5] (q ^ 30 - 1) = 1 := hone_of_not_four_dvd 30 (by norm_num)
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [h2, h8, h12, h14, h18, h20, h24, h30]
  rw [ordProj_five_four_sub_one_eq_sq_add_one hq h5]
  have hexp : ordProj[5] (q * q + 1) ^ 4 * 5 =
      5 ^ (4 * (q * q + 1).factorization 5 + 1) := by
    rw [show ordProj[5] (q * q + 1) ^ 4 = 5 ^ (4 * (q * q + 1).factorization 5) by
      rw [pow_mul']]
    rw [← pow_succ]
  rw [← hexp]
  ring

theorem factorization_card_adjointGroup_E8_five {K : Type} [Field K] [Finite K]
    (h5 : 5 ∣ Nat.card K * Nat.card K + 1) :
    (Nat.card (adjointGroup Tag.E8 K)).factorization 5 =
      4 * (Nat.card K * Nat.card K + 1).factorization 5 + 1 := by
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  have hpq : ¬ 5 ∣ Nat.card K := five_not_dvd_of_dvd_sq_add_one h5
  have hformula := (CFSG.RankThree.OrdinaryECrossPrime.ordinary_E_exact_cross_prime_order_parts
      (K := K) (p := 5) (by norm_num) (by norm_num) hpq).2.2
  have hprod := five_factors_prod hq h5
  apply Nat.pow_right_injective (by norm_num : 2 ≤ 5)
  change 5 ^ (Nat.card (adjointGroup Tag.E8 K)).factorization 5 =
    5 ^ (4 * (Nat.card K * Nat.card K + 1).factorization 5 + 1)
  rw [hformula]
  exact hprod

end Order

end NoOffE8Five

end CFSG.StandardType
