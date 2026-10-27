module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureCyclicRoot

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.CyclicPair

open CFSG.Open CFSG.BenderSuzuki
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

universe u

variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
theorem proper_pair_class_in_point_mem_root
    {H : Subgroup G} {z : G} {x : G} (h : InvolutionPointLocalEmbedding H z)
    (hx : x ∈ involutionPointClass z) (hxH : x ∈ H) :
    x ∈ minimalLocalFailurePairActionPointHull H z := by
  obtain ⟨g, rfl⟩ := hx
  have hgH : g ∈ H := (pointClass_conjugate_mem_iff h g).mp hxH
  exact Subgroup.subset_closure (show rightConjugateElem z g ∈ conjugacyWithin H z from
    ⟨⟨g, hgH⟩, rfl⟩)

theorem proper_pair_even_class_product_commutes
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    {r s : G} (hr : r ∈ involutionPointClass z) (hs : s ∈ involutionPointClass z)
    (heven : Even (orderOf (r * s))) : Commute r s := by
  let Q := minimalLocalFailurePairActionPointHull H z
  obtain ⟨_, _, _, hQ, _, _, hzQ⟩ := proper_pair_point_root h hcomm hbeta ht hproper
  have hrorder := order_two_of_mem_pointClass h.local_datum.distinguished_order hr
  have hsorder := order_two_of_mem_pointClass h.local_datum.distinguished_order hs
  have hsrEven : Even (orderOf (s * r)) := by
    rw [← involution_product_order_swap hrorder hsorder]
    exact heven
  obtain ⟨g, rfl⟩ := hr
  let e : G ≃* G := MulAut.conj g
  have hez : e (rightConjugateElem z g) = z := by
    simp only [e, MulAut.conj_apply, rightConjugateElem]
    group
  have hesclass : e s ∈ involutionPointClass z := by
    simpa only [e, MulAut.conj_apply, rightConjugateElem, inv_inv] using
      pointClass_right_conjugate_mem hs g⁻¹
  have hesEven : Even (orderOf (e s * z)) := by
    rw [← hez, ← map_mul, e.orderOf_eq]
    exact hsrEven
  have hesH : e s ∈ H := pointClass_mem_of_even_product_order h.local_datum hesclass hesEven
  have hesQ : e s ∈ Q := proper_pair_class_in_point_mem_root h.local_datum hesclass hesH
  have hcomm' : e s * z = z * e s :=
    congrArg (fun x : Q => (x : G))
      ((isMulCommutative_iff.mp hQ.1) (⟨e s, hesQ⟩ : Q) (⟨z, hzQ⟩ : Q))
  apply e.injective
  simpa only [map_mul, hez] using hcomm'.symm

theorem proper_pair_distinct_commuting_class_product_mem
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    {r s : G} (hr : r ∈ involutionPointClass z) (hs : s ∈ involutionPointClass z)
    (hne : r ≠ s) (hrs : Commute r s) : r * s ∈ involutionPointClass z := by
  let Q := minimalLocalFailurePairActionPointHull H z
  obtain ⟨_, _, _, _, _, _, hzQ⟩ := proper_pair_point_root h hcomm hbeta ht hproper
  have hQclass := (proper_pair_point_root_classes h hcomm hbeta ht hproper).1
  have hrorder := order_two_of_mem_pointClass h.local_datum.distinguished_order hr
  have hsorder := order_two_of_mem_pointClass h.local_datum.distinguished_order hs
  have hsq : (s * r) ^ 2 = 1 := by
    rw [hrs.symm.mul_pow, (orderOf_eq_prime_iff.mp hsorder).1,
      (orderOf_eq_prime_iff.mp hrorder).1, one_mul]
  have hsrne : s * r ≠ 1 := by
    intro heq
    have heq' := congrArg (fun x : G => x * r) heq
    have hrself : r * r = 1 := by
      simpa only [pow_two] using (orderOf_eq_prime_iff.mp hrorder).1
    have hsr : s = r := by simpa only [mul_assoc, hrself, mul_one, one_mul] using heq'
    exact hne hsr.symm
  have hsrorder : orderOf (s * r) = 2 := orderOf_eq_prime hsq hsrne
  obtain ⟨g, rfl⟩ := hr
  let e : G ≃* G := MulAut.conj g
  have hez : e (rightConjugateElem z g) = z := by
    simp only [e, MulAut.conj_apply, rightConjugateElem]
    group
  have hesclass : e s ∈ involutionPointClass z := by
    simpa only [e, MulAut.conj_apply, rightConjugateElem, inv_inv] using
      pointClass_right_conjugate_mem hs g⁻¹
  have hesEven : Even (orderOf (e s * z)) := by
    rw [← hez, ← map_mul, e.orderOf_eq, hsrorder]
    exact ⟨1, rfl⟩
  have hesH : e s ∈ H := pointClass_mem_of_even_product_order h.local_datum hesclass hesEven
  have hesQ : e s ∈ Q := proper_pair_class_in_point_mem_root h.local_datum hesclass hesH
  have hprodQ : z * e s ∈ Q := Q.mul_mem hzQ hesQ
  have hprodne : z * e s ≠ 1 := by
    intro heq
    have hconj := e.injective (show e (rightConjugateElem z g * s) = e 1 by
      simpa only [map_mul, map_one, hez] using heq)
    have heq' := congrArg (fun x : G => rightConjugateElem z g * x) hconj
    have hrself : rightConjugateElem z g * rightConjugateElem z g = 1 := by
      simpa only [pow_two] using (orderOf_eq_prime_iff.mp hrorder).1
    have hsr : s = rightConjugateElem z g := by
      simpa only [← mul_assoc, hrself, one_mul, mul_one] using heq'
    exact hne hsr.symm
  have hprodHclass : z * e s ∈ conjugacyWithin H z :=
    hQclass ▸ (show z * e s ∈ (Q : Set G) \ {1} from
      ⟨hprodQ, fun hone => hprodne (Set.mem_singleton_iff.mp hone)⟩)
  have hprodclass : z * e s ∈ involutionPointClass z := by
    obtain ⟨a, ha⟩ := hprodHclass
    exact ⟨a, ha⟩
  have hback := pointClass_right_conjugate_mem hprodclass g
  have hbackeq : rightConjugateElem (z * e s) g = rightConjugateElem z g * s := by
    simp only [e, MulAut.conj_apply, rightConjugateElem]
    group
  exact hbackeq ▸ hback

end CFSG.ShultStronglyClosedTI.CyclicPair
