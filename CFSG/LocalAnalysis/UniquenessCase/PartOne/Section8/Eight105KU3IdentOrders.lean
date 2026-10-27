module

import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2TypeDet
import CFSG.Quasithin.Vol2.GoldschmidtF134OddSporSmall
import CFSG.RankThree.PartTwo.Sec19.Step1911Proof
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem odd_of_two_pow_mod_three {f : ℕ} (hf : 2 ^ f % 3 = 2) : Odd f := by
  by_contra h
  have hf_even : Even f := Nat.not_odd_iff_even.mp h
  obtain ⟨k, rfl⟩ := hf_even
  have hpow : 2 ^ (k + k) % 3 = 1 := by
    have h4 : (4 : ℕ) ≡ 1 [MOD 3] := by decide
    have hk := h4.pow k
    have h2 : 2 ^ (k + k) = 4 ^ k := by
      rw [pow_add, ← Nat.mul_pow]
    rw [h2]
    have hk' : 4 ^ k % 3 = 1 := by
      have hk2 := hk
      rw [Nat.ModEq] at hk2
      norm_num at hk2
      exact hk2
    exact hk'
  omega

private theorem gcd_three_two_pow_sub_one (f : ℕ) (hf : 2 ^ f % 3 = 2) :
    Nat.gcd 3 (2 ^ f - 1) = 1 := by
  have hdiv := Nat.div_add_mod (2 ^ f) 3
  have hEq : 2 ^ f - 1 = 3 * (2 ^ f / 3) + 1 := by omega
  have hnot : ¬ 3 ∣ 2 ^ f - 1 := by
    intro h
    have h0 : (2 ^ f - 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd h
    omega
  exact Nat.Coprime.gcd_eq_one ((Nat.prime_three.coprime_iff_not_dvd).mpr hnot)

private theorem orderOf_two_dvd_of_dvd_pow_sub_one {ℓ a : ℕ} (hdvd : ℓ ∣ 2 ^ a - 1) :
    orderOf (2 : ZMod ℓ) ∣ a := by
  have h0 : ((2 ^ a - 1 : ℕ) : ZMod ℓ) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    exact hdvd
  have hc : ((2 ^ a - 1 : ℕ) : ZMod ℓ) = (2 : ZMod ℓ) ^ a - 1 := by
    rw [Nat.cast_sub (Nat.one_le_two_pow)]
    push_cast
    ring
  rw [hc] at h0
  exact orderOf_dvd_of_pow_eq_one (sub_eq_zero.mp h0)

private theorem orderOf_two_dvd_four_mul_and_not_two_mul {ℓ n : ℕ} (hℓ : ℓ.Prime)
    (hodd : Odd ℓ) (hdvd : ℓ ∣ 2 ^ (2 * n) + 1) :
    orderOf (2 : ZMod ℓ) ∣ 4 * n ∧ ¬ orderOf (2 : ZMod ℓ) ∣ 2 * n := by
  have hℓ2 : ℓ ≠ 2 := by
    intro h
    subst h
    exact hodd.not_two_dvd_nat (dvd_refl 2)
  have h0 : ((2 ^ (2 * n) + 1 : ℕ) : ZMod ℓ) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    exact hdvd
  have hpow : (2 : ZMod ℓ) ^ (2 * n) = -1 := by
    have h0' : (2 : ZMod ℓ) ^ (2 * n) + 1 = 0 := by
      simpa using h0
    exact eq_neg_iff_add_eq_zero.mpr h0'
  have hne : (-1 : ZMod ℓ) ≠ 1 := by
    intro h
    have h2 : (2 : ZMod ℓ) = 0 := by
      have h' : (1 : ZMod ℓ) - (-1) = 0 := by
        rw [h]
        exact sub_self 1
      rw [← h']
      ring
    have h2' : ((2 : ℕ) : ZMod ℓ) = 0 := by simpa using h2
    rw [ZMod.natCast_eq_zero_iff] at h2'
    have hle : ℓ ≤ 2 := Nat.le_of_dvd (by norm_num) h2'
    have hge : 2 ≤ ℓ := hℓ.two_le
    exact hℓ2 (by omega)
  constructor
  · rw [orderOf_dvd_iff_pow_eq_one]
    rw [show 4 * n = 2 * n * 2 by ring, pow_mul, hpow]
    norm_num
  · rw [orderOf_dvd_iff_pow_eq_one]
    intro h
    exact hne (by rw [← hpow, h])

private theorem dvd_two_mul_of_dvd_four_mul_of_dvd_two_mul {o n f : ℕ} (hf : Odd f)
    (h4 : o ∣ 4 * n) (h2f : o ∣ 2 * f) : o ∣ 2 * n := by
  have hg : o ∣ Nat.gcd (4 * n) (2 * f) := Nat.dvd_gcd h4 h2f
  rw [show 4 * n = 2 * (2 * n) by ring, Nat.gcd_mul_left] at hg
  have hdvdn : Nat.gcd (2 * n) f ∣ n := by
    have hdf : Nat.gcd (2 * n) f ∣ f := Nat.gcd_dvd_right _ _
    have hodd : Odd (Nat.gcd (2 * n) f) := Odd.of_dvd_nat hf hdf
    have hcop : Nat.Coprime (Nat.gcd (2 * n) f) 2 := Odd.coprime_two_right hodd
    have hdvd : Nat.gcd (2 * n) f ∣ n * 2 := by
      rw [mul_comm n 2]
      exact Nat.gcd_dvd_left _ _
    exact hcop.dvd_of_dvd_mul_right hdvd
  exact hg.trans (Nat.mul_dvd_mul_left 2 hdvdn)

private theorem dvd_two_mul_of_dvd_four_mul_of_dvd_three_mul {o n f : ℕ} (hf : Odd f)
    (h4 : o ∣ 4 * n) (h3f : o ∣ 3 * f) : o ∣ 2 * n := by
  have hg : o ∣ Nat.gcd (4 * n) (3 * f) := Nat.dvd_gcd h4 h3f
  have hodd3f : Odd (3 * f) := Odd.mul (by decide) hf
  have hoddg : Odd (Nat.gcd (4 * n) (3 * f)) :=
    Odd.of_dvd_nat hodd3f (Nat.gcd_dvd_right _ _)
  have hcop2 : Nat.Coprime (Nat.gcd (4 * n) (3 * f)) 2 := Odd.coprime_two_right hoddg
  have hcop4 : Nat.Coprime (Nat.gcd (4 * n) (3 * f)) 4 := by
    simpa using Nat.Coprime.pow_right 2 hcop2
  have hdvd : Nat.gcd (4 * n) (3 * f) ∣ n * 4 := by
    rw [mul_comm n 4]
    exact Nat.gcd_dvd_left _ _
  have hdn : Nat.gcd (4 * n) (3 * f) ∣ n := hcop4.dvd_of_dvd_mul_right hdvd
  exact hg.trans (hdn.trans (by simpa [mul_comm] using Nat.dvd_mul_right n 2))

private theorem prime_dvd_of_dvd_ordA_two {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hgcd : Nat.gcd 3 (2 ^ f - 1) = 1) (hdvd : ℓ ∣ ordA 2 (2 ^ f)) :
    ℓ ∣ (2 ^ f) ^ 2 - 1 ∨ ℓ ∣ (2 ^ f) ^ 3 - 1 := by
  have h := CFSG.RankThree.PartTwo.Sec19.Step1911Proof.ordA_two_mul_gcd f
  rw [hgcd, mul_one] at h
  rw [h] at hdvd
  rcases hℓ.dvd_mul.mp hdvd with h2 | h2
  · have hℓ2' : ℓ ∣ 2 := hℓ.dvd_of_dvd_pow h2
    have hle : ℓ ≤ 2 := Nat.le_of_dvd (by norm_num) hℓ2'
    have hge : 2 ≤ ℓ := hℓ.two_le
    exact absurd (by omega : ℓ = 2) hℓ2
  · rcases hℓ.dvd_mul.mp h2 with hA | hB
    · exact Or.inl hA
    · exact Or.inr hB

theorem false_of_isSpor_j1 {X : Type} [Group X] [Finite X] (hX : IsSpor X .J1) (K : Subgroup X)
    {m : ℕ} (hm : 4 ≤ m) (hL2 : IsL2 (Bar2 K) m) : False := by
  obtain ⟨e⟩ := hX
  have hm1 : 1 ≤ m := by omega
  have hcard := CFSG.SeitzReduction.RankOne.card_of_lieModel_PSL_two_two hL2
  have h2m : 2 ^ m ∣ Nat.card (Bar2 K) := by
    rw [hcard, CFSG.RankThree.PartOne.S12K.ordA_one_eq hm1]
    exact dvd_mul_right _ _
  have hdq : Nat.card (Bar2 K) ∣ Nat.card K := Subgroup.card_quotient_dvd_card _
  have hdK : Nat.card K ∣ Nat.card X := Subgroup.card_subgroup_dvd_card K
  have h16 : 16 ∣ Nat.card X := by
    have hpow : 2 ^ 4 ∣ 2 ^ m := pow_dvd_pow 2 hm
    exact hpow.trans (h2m.trans (hdq.trans hdK))
  have hXc : Nat.card X = 175560 := by
    rw [Nat.card_congr e.toEquiv, CFSG.Quasithin.H13.NQCore.card_carrier_j1]
  rw [hXc] at h16
  norm_num at h16

theorem false_of_psl_three_two_odd {X : Type} [Group X] [Finite X] {f : ℕ}
    (hX : LieModel X .PSL 3 2 f) (hf : 2 ^ f % 3 = 2) (K : Subgroup X) (n : ℕ)
    (hL2 : IsL2 (Bar2 K) (2 * n)) : False := by
  have hn : 1 ≤ n := by
    have h2 := CFSG.SeitzReduction.RankOne.two_le_of_lieModel_PSL_two_two hL2
    omega
  have hgcd : Nat.gcd 3 (2 ^ f - 1) = 1 := gcd_three_two_pow_sub_one f hf
  have hfodd : Odd f := odd_of_two_pow_mod_three hf
  have hBK : Nat.card (Bar2 K) = 2 ^ (2 * n) * ((2 ^ (2 * n)) ^ 2 - 1) := by
    rw [CFSG.SeitzReduction.RankOne.card_of_lieModel_PSL_two_two hL2,
      CFSG.RankThree.PartOne.S12K.ordA_one_eq (by omega : 1 ≤ 2 * n)]
  have hdiv : 2 ^ (2 * n) + 1 ∣ Nat.card (Bar2 K) := by
    have hsq : 2 ^ (2 * n) + 1 ∣ (2 ^ (2 * n)) ^ 2 - 1 := by
      rw [show (1 : ℕ) = 1 ^ 2 by norm_num, Nat.sq_sub_sq]
      exact dvd_mul_right _ _
    rw [hBK]
    exact dvd_mul_of_dvd_right hsq _
  have hodd : Odd (2 ^ (2 * n) + 1) := by
    have hr := CFSG.Timmesfeld.Orders.odd_pow_add_one (f := 1) (a := 2 * n)
      (by norm_num) (by omega)
    simpa using hr
  have hgt : 1 < 2 ^ (2 * n) := Nat.one_lt_two_pow (by omega)
  obtain ⟨ℓ, hℓ, hℓdvd⟩ := Nat.exists_prime_and_dvd (show 2 ^ (2 * n) + 1 ≠ 1 by omega)
  have hℓodd : Odd ℓ := Odd.of_dvd_nat hodd hℓdvd
  have hℓ2 : ℓ ≠ 2 := by
    intro h
    subst h
    exact hℓodd.not_two_dvd_nat (dvd_refl 2)
  have hℓBK : ℓ ∣ Nat.card (Bar2 K) := hℓdvd.trans hdiv
  have hXK : Nat.card (Bar2 K) ∣ Nat.card X :=
    (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥K)).trans
      (Subgroup.card_subgroup_dvd_card K)
  have hℓX : ℓ ∣ Nat.card X := hℓBK.trans hXK
  have hXc : Nat.card X = ordA 2 (2 ^ f) :=
    CFSG.GH74.card_of_lieModel_PSL (n := 3) (p := 2) (f := f) (by norm_num) hX
  rw [hXc] at hℓX
  have hAorB := prime_dvd_of_dvd_ordA_two hℓ hℓ2 hgcd hℓX
  obtain ⟨h4n, hnot2n⟩ := orderOf_two_dvd_four_mul_and_not_two_mul hℓ hℓodd hℓdvd
  rcases hAorB with hA | hB
  · have h2f : orderOf (2 : ZMod ℓ) ∣ 2 * f := by
      have hA' : ℓ ∣ 2 ^ (2 * f) - 1 := by
        simpa [← pow_mul, Nat.mul_comm] using hA
      exact orderOf_two_dvd_of_dvd_pow_sub_one hA'
    exact hnot2n (dvd_two_mul_of_dvd_four_mul_of_dvd_two_mul hfodd h4n h2f)
  · have h3f : orderOf (2 : ZMod ℓ) ∣ 3 * f := by
      have hB' : ℓ ∣ 2 ^ (3 * f) - 1 := by
        simpa [← pow_mul, Nat.mul_comm] using hB
      exact orderOf_two_dvd_of_dvd_pow_sub_one hB'
    exact hnot2n (dvd_two_mul_of_dvd_four_mul_of_dvd_three_mul hfodd h4n h3f)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
