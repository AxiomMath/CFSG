module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureInvertedHullData

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionSubgroupSylow

universe u

variable {G : Type u} [Group G]

@[expose] def minimalLocalFailurePairConfinementClosure (P : Subgroup G) (z : G) :
    Subgroup G := Subgroup.closure (minimalLocalFailureInvertedSet P z)

theorem pairConfinement_closure_le (P : Subgroup G) (z : G) :
    minimalLocalFailurePairConfinementClosure P z ≤ P :=
  (Subgroup.closure_le P).mpr fun _ hx => hx.1

theorem pairConfinement_closure_contains (P : Subgroup G) (z : G) :
    minimalLocalFailureInvertedSet P z ⊆ minimalLocalFailurePairConfinementClosure P z :=
  Subgroup.subset_closure

theorem pairConfinement_closure_normalizer (P : Subgroup G) (z : G)
    (hz : orderOf z = 2) :
    minimalLocalFailureInvertedOvergroup P z ≤
      Subgroup.normalizer (minimalLocalFailurePairConfinementClosure P z : Set G) :=
  (invertedHull_overgroup_normalizes_set P z hz).trans
    (Subgroup.normalizer_le_normalizer_closure _)

theorem pairConfinement_actions_agree (P : Subgroup G) (z s : G)
    (hs : ∀ x ∈ minimalLocalFailureInvertedSet P z, rightConjugateElem x s = x⁻¹) :
    ∀ x ∈ minimalLocalFailurePairConfinementClosure P z,
      rightConjugateElem x s = rightConjugateElem x z := by
  have hgenerators : Set.EqOn (MulAut.conj s⁻¹).toMonoidHom
      (MulAut.conj z⁻¹).toMonoidHom (minimalLocalFailureInvertedSet P z) := by
    intro x hx
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, rightConjugateElem]
      using (hs x hx).trans hx.2.symm
  intro x hx
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, rightConjugateElem]
    using MonoidHom.eqOn_closure hgenerators hx

theorem pairConfinement_closure_inverted_set (P : Subgroup G) (z s : G)
    (hs : ∀ x ∈ minimalLocalFailureInvertedSet P z, rightConjugateElem x s = x⁻¹) :
    minimalLocalFailureInvertedSet (minimalLocalFailurePairConfinementClosure P z) s =
      minimalLocalFailureInvertedSet P z := by
  ext x
  constructor
  · rintro ⟨hx, hxs⟩
    exact ⟨pairConfinement_closure_le P z hx,
      (pairConfinement_actions_agree P z s hs x hx).symm.trans hxs⟩
  · intro hx
    exact ⟨pairConfinement_closure_contains P z hx, hs x hx⟩

def pairConfinement_inverted_equiv_class [Finite G]
    (P : Subgroup G) (hPodd : Odd (Nat.card P)) (z : G) (hz : orderOf z = 2)
    (hzP : z ∈ Subgroup.normalizer (P : Set G)) :
    minimalLocalFailureInvertedSet P z ≃ conjugacyWithin P z := by
  have hzz : z * z = 1 := by
    simpa only [pow_two] using (orderOf_eq_prime_iff.mp hz).1
  have hzinv : z⁻¹ = z := inv_eq_self_of_orderOf_eq_two hz
  refine
    { toFun := fun x => ⟨x.val * z,
        inverted_odd_element_mul_involution_conjugate P hPodd hzz x.property.1 x.property.2⟩
      invFun := fun s => ⟨s.val * z, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · obtain ⟨a, ha⟩ := s.property
    have hza : z * (a : G) * z⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp hzP (a : G)).mp a.property
    have hmem : s.val * z ∈ P := by
      rw [← ha]
      simpa only [hzinv, mul_assoc] using P.mul_mem (P.inv_mem a.property) hza
    refine ⟨hmem, ?_⟩
    have hsinv : s.val⁻¹ = s.val :=
      inv_eq_self_of_orderOf_eq_two (order_two_of_mem_pointClass hz
        ⟨(a : G), ha⟩)
    change z⁻¹ * (s.val * z) * z = (s.val * z)⁻¹
    rw [mul_inv_rev, hzinv, hsinv]
    simp only [mul_assoc, hzz, mul_one]
  · intro x
    apply Subtype.ext
    change x.val * z * z = x.val
    rw [mul_assoc, hzz, mul_one]
  · intro s
    apply Subtype.ext
    change s.val * z * z = s.val
    rw [mul_assoc, hzz, mul_one]

theorem pairConfinement_inverted_card_eq_class [Finite G]
    (P : Subgroup G) (hPodd : Odd (Nat.card P)) (z : G) (hz : orderOf z = 2)
    (hzP : z ∈ Subgroup.normalizer (P : Set G)) :
    Nat.card (minimalLocalFailureInvertedSet P z) = Nat.card (conjugacyWithin P z) :=
  Nat.card_congr (pairConfinement_inverted_equiv_class P hPodd z hz hzP)

theorem pairConfinement_closure_class_card [Finite G]
    (P : Subgroup G) (hPodd : Odd (Nat.card P)) (z s : G)
    (hz : orderOf z = 2) (hsorder : orderOf s = 2)
    (hzP : z ∈ Subgroup.normalizer (P : Set G))
    (hsV : s ∈ Subgroup.normalizer (minimalLocalFailurePairConfinementClosure P z : Set G))
    (hs : ∀ x ∈ minimalLocalFailureInvertedSet P z, rightConjugateElem x s = x⁻¹) :
    Nat.card (conjugacyWithin (minimalLocalFailurePairConfinementClosure P z) s) =
      Nat.card (conjugacyWithin P z) := by
  have hVodd : Odd (Nat.card (minimalLocalFailurePairConfinementClosure P z)) :=
    hPodd.of_dvd_nat (Subgroup.card_dvd_of_le (pairConfinement_closure_le P z))
  rw [← pairConfinement_inverted_card_eq_class _ hVodd s hsorder hsV,
    pairConfinement_closure_inverted_set P z s hs]
  exact pairConfinement_inverted_card_eq_class P hPodd z hz hzP

theorem pairConfinement_inverted_nonidentity_of_card [Finite G]
    (P : Subgroup G) (z : G) (hcard : 1 < Nat.card (minimalLocalFailureInvertedSet P z)) :
    ∃ x ∈ minimalLocalFailureInvertedSet P z, x ≠ 1 := by
  by_contra hnone
  have hall : ∀ x ∈ minimalLocalFailureInvertedSet P z, x = 1 := by
    intro x hx
    by_contra hne
    exact hnone ⟨x, hx, hne⟩
  let : Subsingleton (minimalLocalFailureInvertedSet P z) :=
    ⟨fun a b => Subtype.ext ((hall a a.property).trans (hall b b.property).symm)⟩
  have hsmall : Nat.card (minimalLocalFailureInvertedSet P z) ≤ 1 :=
    Finite.card_le_one_iff_subsingleton.mpr inferInstance
  omega

end CFSG.ShultStronglyClosedTI
