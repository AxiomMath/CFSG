module

public import CFSG.RankThree.PartTwo.Sec15.F153A10KDefs

public section

namespace CFSG.RankThree.PartTwo.Sec15.F153A10K

open Equiv

theorem cycleType_of_sq_eq_one {x : Perm (Fin 10)} (hx2 : x ^ 2 = 1) :
    x.cycleType = Multiset.replicate (x.support.card / 2) 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrep : x.cycleType = Multiset.replicate (Multiset.card x.cycleType) 2 :=
    Equiv.Perm.cycleType_of_pow_prime_eq_one hx2
  have hsum : x.cycleType.sum = x.support.card := Equiv.Perm.sum_cycleType x
  have hsum2 : x.cycleType.sum = 2 * Multiset.card x.cycleType := by
    conv_lhs => rw [hrep]
    rw [Multiset.sum_replicate, smul_eq_mul]
    ring
  have hsupp : x.support.card = 2 * Multiset.card x.cycleType := by omega
  rw [hsupp, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  exact hrep

theorem card_support_of_involution {x : Perm (Fin 10)} (hxA : x ∈ alternatingGroup (Fin 10))
    (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1) : x.support.card = 4 ∨ x.support.card = 8 := by
  have hcyc : x.cycleType = Multiset.replicate (x.support.card / 2) 2 :=
    cycleType_of_sq_eq_one hx2
  have hcard : Multiset.card x.cycleType = x.support.card / 2 := by
    rw [hcyc, Multiset.card_replicate]
  have hsum2 : x.cycleType.sum = x.support.card / 2 * 2 := by
    rw [hcyc, Multiset.sum_replicate, smul_eq_mul]
  have hsupp : x.support.card = x.support.card / 2 * 2 := by
    have := Equiv.Perm.sum_cycleType x
    omega
  have hle : x.support.card ≤ 10 := by
    have := Finset.card_le_univ x.support
    simpa using this
  have hc0 : x.support.card / 2 ≠ 0 := by
    intro h0
    apply hx1
    rw [← Equiv.Perm.cycleType_eq_zero, hcyc, h0, Multiset.replicate_zero]
  have hsgn : Equiv.Perm.sign x = 1 := Equiv.Perm.mem_alternatingGroup.1 hxA
  have hsgn' : (-1 : ℤˣ) ^ (x.cycleType.sum + Multiset.card x.cycleType) = 1 :=
    (Equiv.Perm.sign_of_cycleType x).symm.trans hsgn
  rw [hsum2, hcard] at hsgn'
  have hneg : (-1 : ℤˣ) ≠ 1 := by decide
  have hev : Even (x.support.card / 2 * 2 + x.support.card / 2) :=
    (neg_one_pow_eq_one_iff_even hneg).1 hsgn'
  have hceven : Even (x.support.card / 2) := by
    obtain ⟨r, hr⟩ := hev
    exact ⟨r - x.support.card / 2, by omega⟩
  obtain ⟨s, hs⟩ := hceven
  omega

theorem exists_conj_eq_tZero {x : Perm (Fin 10)} (hx2 : x ^ 2 = 1) (hx4 : x.support.card = 4) :
    ∃ σ : Perm (Fin 10), σ * x * σ⁻¹ = tZero := by
  have hT2 : tZero ^ 2 = 1 := by
    unfold tZero
    decide +kernel
  have hTc : tZero.support.card = 4 := by
    unfold tZero
    decide +kernel
  have hcyc : x.cycleType = tZero.cycleType := by
    rw [cycleType_of_sq_eq_one hx2, cycleType_of_sq_eq_one hT2, hx4, hTc]
  exact isConj_iff.1 (Equiv.Perm.isConj_iff_cycleType_eq.2 hcyc)

theorem exists_conj_eq_tOne {x : Perm (Fin 10)} (hx2 : x ^ 2 = 1) (hx8 : x.support.card = 8) :
    ∃ σ : Perm (Fin 10), σ * x * σ⁻¹ = tOne := by
  have hT2 : tOne ^ 2 = 1 := by
    unfold tOne
    decide +kernel
  have hTc : tOne.support.card = 8 := by
    unfold tOne
    decide +kernel
  have hcyc : x.cycleType = tOne.cycleType := by
    rw [cycleType_of_sq_eq_one hx2, cycleType_of_sq_eq_one hT2, hx8, hTc]
  exact isConj_iff.1 (Equiv.Perm.isConj_iff_cycleType_eq.2 hcyc)

end CFSG.RankThree.PartTwo.Sec15.F153A10K

