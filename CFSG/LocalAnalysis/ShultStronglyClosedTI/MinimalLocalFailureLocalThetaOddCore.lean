module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.OddCorePrimeComplementGrowthCore

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.LocalTheta

open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.BenderSuzuki.PFAppendixIII
open CFSG.BenderSuzuki.PFchapter1section1
open scoped commutatorElement

universe u

variable {G : Type u} [Group G] [Finite G]

theorem normal_prime_complement_member_centralizes {p : ℕ} (hp : p.Prime)
    (W A : Subgroup G) [W.Normal] (hWcoprime : Nat.Coprime p (Nat.card W))
    (hA : IsPGroup p A) {z : G} (hzW : z ∈ W)
    (hzA : z ∈ Subgroup.normalizer (A : Set G)) :
    A ≤ Subgroup.centralizer ({z} : Set G) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := hA.exists_card_eq
  have hdis : Disjoint W A := Subgroup.disjoint_of_coprime_natCard (by
    rw [hn]
    exact hWcoprime.symm.pow_right n)
  intro a ha
  have hcommA : ⁅z, a⁆ ∈ A :=
    A.mul_mem ((Subgroup.mem_normalizer_iff.mp hzA a).mp ha) (A.inv_mem ha)
  have hcommW : ⁅z, a⁆ ∈ W := by
    have hh := W.mul_mem hzW
      ((inferInstance : W.Normal).conj_mem z⁻¹ (W.inv_mem hzW) a)
    simpa only [commutatorElement_def, mul_assoc] using hh
  have hone : ⁅z, a⁆ = 1 := Subgroup.disjoint_def.mp hdis hcommW hcommA
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (commutatorElement_eq_one_iff_mul_comm.mp hone).symm

theorem prime_complement_core_odd_of_involution_class {p : ℕ} (hp : p.Prime) {z : G}
    (T A : Subgroup G) (hclass : ∀ v : G, IsInvolution v → v ∈ conjugacyWithin T z)
    (hA : IsPGroup p A) (hAz : rightConjugate A z = A)
    (hnoncentral : ¬ A ≤ Subgroup.centralizer ({z} : Set G)) :
    Odd (Nat.card (pPrimeCore p G)) := by
  let : Fact p.Prime := ⟨hp⟩
  let W := pPrimeCore p G
  by_contra hnotodd
  have heven : Even (Nat.card W) := Nat.not_odd_iff_even.mp hnotodd
  obtain ⟨v, hvorder⟩ := exists_prime_orderOf_dvd_card' (G := W) 2 heven.two_dvd
  have hvGorder : orderOf (v : G) = 2 := (Subgroup.orderOf_coe v).trans hvorder
  have hvi : IsInvolution (v : G) :=
    ⟨(orderOf_eq_prime_iff.mp hvGorder).2, (orderOf_eq_prime_iff.mp hvGorder).1⟩
  obtain ⟨t, ht⟩ := hclass v hvi
  have hzW : z ∈ W := by
    have hh := (inferInstance : W.Normal).conj_mem v.val v.property t.val
    rw [← ht] at hh
    simpa only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_right,
      mul_inv_cancel, mul_one] using hh
  exact hnoncentral (normal_prime_complement_member_centralizes hp W A
    pPrimeCore_coprime_card hA hzW (invariant_subgroup_mem_normalizer hAz))

omit [Finite G] in
theorem odd_prime_complement_core_le_odd_core {p : ℕ}
    (hodd : Odd (Nat.card (pPrimeCore p G))) : pPrimeCore p G ≤ oddCore G := by
  unfold oddCore
  exact le_sSup ⟨inferInstance, hodd⟩

theorem normal_prime_complement_le_core_of_full_prime_part {p : ℕ} (hp : p.Prime)
    (U K C : Subgroup G) [Group.IsSolvable K]
    (hUK : U ≤ K) (hCU : C ≤ U) (hCnormal : (C.subgroupOf U).Normal)
    (hCcoprime : Nat.Coprime p (Nat.card C))
    (hpart : CFSG.OrderReductions.PrimePart.primePart p (Nat.card U) =
      CFSG.OrderReductions.PrimePart.primePart p (Nat.card K)) :
    C ≤ (pPrimeCore p K).map K.subtype := by
  let : Fact p.Prime := ⟨hp⟩
  have hCcard : Nat.card (C.subgroupOf U) = Nat.card C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCU).toEquiv
  have hsmall : C.subgroupOf U ≤ pPrimeCore p U := by
    unfold pPrimeCore
    exact le_sSup ⟨hCnormal, hCcard.symm ▸ hCcoprime⟩
  have hmap : C ≤ (pPrimeCore p U).map U.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hCU]
    exact Subgroup.map_mono hsmall
  have hgrowth := primeComplementGrowth_full_prime_part_core_le p U K hUK hpart
  rw [← pPrimeCore_eq_piCore, ← pPrimeCore_eq_piCore] at hgrowth
  exact hmap.trans hgrowth

end CFSG.ShultStronglyClosedTI.LocalTheta
