module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureAmbientDegreeFiber
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.InvolutionCountingOrderFormula

public section

namespace CFSG.ShultStronglyClosedTI.AmbientDegree

open CFSG.ShultStronglyClosedTI
open CFSG.ShultStronglyClosedTI.MixedClass
open CFSG.ShultStronglyClosedTI.PairInvolutionFixedField
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem mem_thompsonPairs_self_iff {H Q : Subgroup G} {z u : G}
    (h : InvolutionPointLocalEmbedding H z) (hQ : CFSG.Open.IsElemAbelian 2 Q)
    (hQclass : (Q : Set G) \ {1} = conjugacyWithin H z) (hu : orderOf u = 2)
    (hUH : involutionPointClass u ∩ (H : Set G) = conjugacyWithin H u)
    (hzpairs : InvolutionCounting.thompsonPairs u z z =
      {p : G × G | IsConj u p.1 ∧ p.1 ∈ Subgroup.centralizer {z} ∧ IsConj z p.2 ∧
        p.2 ∈ Subgroup.centralizer {z} ∧ (p.1 * p.2) ^ 2 = z})
    (p : G × G) :
    p ∈ InvolutionCounting.thompsonPairs u z z ↔
      (p.1 ∈ conjugacyWithin H u ∧ p.1 ∈ Subgroup.centralizer ({z} : Set G)) ∧
        (p.2 ∈ Q ∧ (p.1 * p.2) ^ 2 = z) := by
  have hzH := point_centralizer_le h
  have hzQ : z ∈ Q := by
    have hz : z ∈ conjugacyWithin H z := ⟨1, by simp⟩
    rw [← hQclass] at hz
    exact hz.1
  rw [hzpairs]
  constructor
  · rintro ⟨h1, h1C, h2, h2C, hsq⟩
    refine ⟨⟨?_, h1C⟩, ?_, hsq⟩
    · rw [← hUH]
      exact ⟨mem_pointClass_iff_isConj.mpr h1, hzH h1C⟩
    · have h2Q : p.2 ∈ (Q : Set G) \ {1} := by
        rw [← class_inter_point h hQclass]
        exact ⟨mem_pointClass_iff_isConj.mpr h2, hzH h2C⟩
      exact h2Q.1
  · rintro ⟨⟨h1, h1C⟩, h2Q, hsq⟩
    have h1U : p.1 ∈ involutionPointClass u := by
      rw [← hUH] at h1
      exact h1.1
    have hv2 : p.1 * p.1 = 1 := InvolutionCounting.mul_self_eq_one_of_isConj
      (mul_self_eq_one_of_orderOf_eq_two hu) (mem_pointClass_iff_isConj.mp h1U)
    have h21 : p.2 ≠ 1 := by
      intro h1'
      rw [h1', mul_one, sq, hv2] at hsq
      have hz := h.distinguished_order
      rw [← hsq, orderOf_one] at hz
      exact absurd hz (by norm_num)
    refine ⟨mem_pointClass_iff_isConj.mp h1U, h1C,
      mem_pointClass_iff_isConj.mp (point_subgroup_class h hQclass ⟨h2Q, h21⟩), ?_, hsq⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hQ.1.is_comm.comm ⟨p.2, h2Q⟩ ⟨z, hzQ⟩))

omit [Finite G] in
theorem thompsonPairCount_self_eq_zero {H Q : Subgroup G} {z u : G}
    (h : InvolutionPointLocalEmbedding H z) (hQ : CFSG.Open.IsElemAbelian 2 Q)
    (hQclass : (Q : Set G) \ {1} = conjugacyWithin H z) (hu : orderOf u = 2)
    (hUH : involutionPointClass u ∩ (H : Set G) = conjugacyWithin H u)
    (hzpairs : InvolutionCounting.thompsonPairs u z z =
      {p : G × G | IsConj u p.1 ∧ p.1 ∈ Subgroup.centralizer {z} ∧ IsConj z p.2 ∧
        p.2 ∈ Subgroup.centralizer {z} ∧ (p.1 * p.2) ^ 2 = z})
    (hQu : Q ≤ Subgroup.centralizer ({u} : Set G)) :
    InvolutionCounting.thompsonPairCount u z z = 0 := by
  have hQnorm := point_subgroup_normalized hQclass
  have hu2 := mul_self_eq_one_of_orderOf_eq_two hu
  refine Nat.card_eq_zero.mpr (Or.inl ⟨fun p => ?_⟩)
  obtain ⟨⟨⟨k, hk⟩, -⟩, h2Q, hsq⟩ :=
    (mem_thompsonPairs_self_iff h hQ hQclass hu hUH hzpairs p).mp p.2
  have hs' : (k : G) * (p : G × G).2 * (k : G)⁻¹ ∈ Q := by
    simpa only [inv_inv] using hQnorm (k : G)⁻¹ (Subgroup.inv_mem _ k.2) _ h2Q
  have hc : Commute ((k : G) * (p : G × G).2 * (k : G)⁻¹) u :=
    Subgroup.mem_centralizer_singleton_iff.mp (hQu hs')
  have hc' := hc.conj (k : G)⁻¹
  rw [inv_inv, show (k : G)⁻¹ * ((k : G) * (p : G × G).2 * (k : G)⁻¹) * (k : G) =
    (p : G × G).2 by group, hk] at hc'
  have hv2 : (p : G × G).1 * (p : G × G).1 = 1 := by
    rw [← hk, show (k : G)⁻¹ * u * k * ((k : G)⁻¹ * u * k) = (k : G)⁻¹ * (u * u) * k by group,
      hu2, mul_one, inv_mul_cancel]
  have hs2 : (p : G × G).2 * (p : G × G).2 = 1 := by rw [← sq]; exact hQ.2 _ h2Q
  have hone : ((p : G × G).1 * (p : G × G).2) ^ 2 = 1 := by
    rw [sq, show (p : G × G).1 * (p : G × G).2 * ((p : G × G).1 * (p : G × G).2) =
      (p : G × G).1 * ((p : G × G).2 * (p : G × G).1) * (p : G × G).2 by group, hc'.eq,
      show (p : G × G).1 * ((p : G × G).1 * (p : G × G).2) * (p : G × G).2 =
        ((p : G × G).1 * (p : G × G).1) * ((p : G × G).2 * (p : G × G).2) by group, hv2, hs2,
      one_mul]
  have hz := h.distinguished_order
  rw [← hsq, hone, orderOf_one] at hz
  exact absurd hz (by norm_num)

theorem thompsonPairCount_self_eq_mul {H Q : Subgroup G} {z u : G}
    (h : InvolutionPointLocalEmbedding H z) (hQ : CFSG.Open.IsElemAbelian 2 Q)
    (hQclass : (Q : Set G) \ {1} = conjugacyWithin H z) (hu : orderOf u = 2) (huH : u ∈ H)
    (hUH : involutionPointClass u ∩ (H : Set G) = conjugacyWithin H u)
    (hzpairs : InvolutionCounting.thompsonPairs u z z =
      {p : G × G | IsConj u p.1 ∧ p.1 ∈ Subgroup.centralizer {z} ∧ IsConj z p.2 ∧
        p.2 ∈ Subgroup.centralizer {z} ∧ (p.1 * p.2) ^ 2 = z})
    (hsq : Nat.card Q = Nat.card (Q ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) ^ 2) :
    InvolutionCounting.thompsonPairCount u z z =
      Nat.card {v : G // v ∈ conjugacyWithin H u ∧ v ∈ Subgroup.centralizer ({z} : Set G)} *
        Nat.card (Q ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) := by
  have hQnorm := point_subgroup_normalized hQclass
  have hu2 := mul_self_eq_one_of_orderOf_eq_two hu
  have hzQ : z ∈ Q := by
    have hz : z ∈ conjugacyWithin H z := ⟨1, by simp⟩
    rw [← hQclass] at hz
    exact hz.1
  rw [InvolutionCounting.thompsonPairCount]
  have hcongr : Nat.card ↥(InvolutionCounting.thompsonPairs u z z) =
      Nat.card {p : G × G // p.1 ∈ {v : G | v ∈ conjugacyWithin H u ∧
        v ∈ Subgroup.centralizer ({z} : Set G)} ∧ (p.2 ∈ Q ∧ (p.1 * p.2) ^ 2 = z)} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun p =>
      mem_thompsonPairs_self_iff h hQ hQclass hu hUH hzpairs p)
  rw [hcongr]
  refine card_pairs_const_fiber {v : G | v ∈ conjugacyWithin H u ∧
    v ∈ Subgroup.centralizer ({z} : Set G)} (fun v s => s ∈ Q ∧ (v * s) ^ 2 = z) _ ?_
  rintro v ⟨⟨k, rfl⟩, hvz⟩
  have hcard := card_inf_centralizer_conj hQclass u k.2
  rw [← hcard]
  apply card_square_fiber hQ
  · rw [show (k : G)⁻¹ * u * k * ((k : G)⁻¹ * u * k) = (k : G)⁻¹ * (u * u) * k by group, hu2,
      mul_one, inv_mul_cancel]
  · exact hQnorm _ (H.mul_mem (H.mul_mem (H.inv_mem k.2) huH) k.2)
  · rw [hcard]
    exact hsq
  · refine ⟨hzQ, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp hvz).symm

end CFSG.ShultStronglyClosedTI.AmbientDegree
