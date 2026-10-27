module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.StrongEmbeddingMaximality
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionGeometryZStarFactorization

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.OrderReductions.InvolutionGraph
open CFSG.Open CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open scoped Pointwise

universe u

variable {G : Type u} [Group G] [Finite G]

theorem invertedHull_odd_normal_centralizer_product
    (H R : Subgroup G) [R.Normal] (hRH : R ≤ H)
    (hRodd : Odd (Nat.card R)) (z : G) (hz : orderOf z = 2)
    (hdifference : ∀ h ∈ H, rightConjugateElem z h * z ∈ R) :
    (H : Set G) = (R : Set G) * (H ⊓ Subgroup.centralizer ({z} : Set G) : Set G) := by
  have hzsq : z * z = 1 := by simpa only [pow_two] using
    (orderOf_eq_prime_iff.mp hz).1
  have hzinv : z⁻¹ = z := inv_eq_self_of_orderOf_eq_two hz
  ext h
  constructor
  · intro hh
    let t := rightConjugateElem z h
    have htsq : t * t = 1 := by
      dsimp [t, rightConjugateElem]
      calc
        (h⁻¹ * z * h) * (h⁻¹ * z * h) = h⁻¹ * (z * z) * h := by group
        _ = 1 := by rw [hzsq]; simp
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htsq
    have hinverted : z⁻¹ * (t * z) * z = (t * z)⁻¹ := by
      rw [hzinv, mul_inv_rev, hzinv, htinv]
      simp only [mul_assoc, hzsq, mul_one]
    have hconjugate := inverted_odd_element_mul_involution_conjugate
      R hRodd hzsq (hdifference h hh) hinverted
    have htz : (t * z) * z = t := by rw [mul_assoc, hzsq, mul_one]
    rw [htz] at hconjugate
    obtain ⟨r, hr⟩ := hconjugate
    let c := h * (r : G)⁻¹
    have hcH : c ∈ H := H.mul_mem hh (H.inv_mem (hRH r.property))
    have hcC : c ∈ Subgroup.centralizer ({z} : Set G) := by
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      have hright : h⁻¹ * z * h = (r : G)⁻¹ * z * r := hr.symm
      have hfix : c⁻¹ * z * c = z := by
        dsimp [c]
        calc
          (h * (r : G)⁻¹)⁻¹ * z * (h * (r : G)⁻¹) =
              (r : G) * (h⁻¹ * z * h) * (r : G)⁻¹ := by group
          _ = z := by rw [hright]; group
      have hh := congrArg (fun t : G => c * t) hfix
      have hcomm : z * c = c * z := by
        simpa only [← mul_assoc, mul_inv_cancel, one_mul] using hh
      exact hcomm.symm
    have hr' : c * (r : G) * c⁻¹ ∈ R :=
      (inferInstance : R.Normal).conj_mem _ r.property c
    exact Set.mem_mul.mpr ⟨c * (r : G) * c⁻¹, hr', c, ⟨hcH, hcC⟩, by
      dsimp [c]
      group⟩
  · rintro ⟨r, hr, c, hc, rfl⟩
    exact H.mul_mem (hRH hr) hc.1

theorem invertedHull_maximal_solvable_core_product
    [Group.IsSolvable G] (H : Subgroup G)
    (hH : CFSG.OrderReductions.InvolutionGraph.StronglyEmbedded H)
    (hmax : IsCoatom H) (z : G) (hz : orderOf z = 2) (hzH : z ∈ H) :
    (H : Set G) = (H.normalCore : Set G) *
      (H ⊓ Subgroup.centralizer ({z} : Set G) : Set G) := by
  let R := H.normalCore
  let q := QuotientGroup.mk' R
  let HQ := H.map q
  have hRodd := CFSG.OrderReductions.StrongEmbedding.normalCore_odd H hH
  have hHQ := CFSG.OrderReductions.StrongEmbeddingInheritance.odd_normal_quotient_stronglyEmbedded
    H hH R H.normalCore_le hRodd
  have hqker : q.ker ≤ H := by
    rw [QuotientGroup.ker_mk']
    exact H.normalCore_le
  have hmaxQ := CFSG.OrderReductions.SolvableMaximal.maximal_map_of_kernel_le
    q (QuotientGroup.mk'_surjective R) H hmax hqker
  have hcoreQ := CFSG.OrderReductions.SolvableMaximal.quotient_core_free H
  have hoddker : Odd (Nat.card q.ker) := by
    dsimp [q]
    simpa only [QuotientGroup.ker_mk'] using hRodd
  let zQ : Involution (G ⧸ R) := ⟨q z,
    CFSG.OrderReductions.OddKernelInvolutions.involution_image_order q hoddker ⟨z, hz⟩⟩
  have hzQ : zQ.val ∈ HQ := Subgroup.mem_map_of_mem q hzH
  apply invertedHull_odd_normal_centralizer_product H R H.normalCore_le hRodd z hz
  intro h hh
  have htorder : orderOf (rightConjugateElem z h) = 2 :=
    order_two_of_mem_pointClass hz ⟨h, rfl⟩
  let tQ : Involution (G ⧸ R) := ⟨q (rightConjugateElem z h),
    CFSG.OrderReductions.OddKernelInvolutions.involution_image_order q hoddker
      ⟨rightConjugateElem z h, htorder⟩⟩
  have htQ : tQ.val ∈ HQ := Subgroup.mem_map_of_mem q
    (H.mul_mem (H.mul_mem (H.inv_mem hh) hzH) hh)
  have heq : tQ = zQ :=
    CFSG.OrderReductions.SolvableMaximal.core_free_involutions_unique
      HQ hHQ hmaxQ hcoreQ tQ zQ htQ hzQ
  have hvalues : q (rightConjugateElem z h) = q z := congrArg Subtype.val heq
  apply (QuotientGroup.eq_one_iff _).mp
  change q (rightConjugateElem z h * z) = 1
  rw [map_mul, hvalues, ← map_mul]
  simpa only [pow_two, map_one] using congrArg q (orderOf_eq_prime_iff.mp hz).1

theorem invertedHull_exists_immediate_overgroup (H : Subgroup G) (hH : H ≠ ⊤) :
    ∃ K : Subgroup G, H < K ∧ IsCoatom (H.subgroupOf K) := by
  obtain ⟨K, _, hminimal⟩ := Finite.exists_le_minimal
    (p := fun K : Subgroup G => H < K) (a := ⊤) (lt_top_iff_ne_top.mpr hH)
  have hHK : H < K := hminimal.prop
  refine ⟨K, hHK, ?_⟩
  constructor
  · intro heq
    exact hHK.not_ge (Subgroup.subgroupOf_eq_top.mp heq)
  · intro B hB
    have hHmap : (H.subgroupOf K).map K.subtype = H :=
      Subgroup.map_subgroupOf_eq_of_le hHK.le
    have hstrict : H < B.map K.subtype := by
      rw [← hHmap]
      exact (Subgroup.map_lt_map_iff_of_injective Subtype.val_injective).mpr hB
    have hmap : B.map K.subtype = K :=
      hminimal.eq_of_le hstrict (Subgroup.map_subtype_le B)
    apply Subgroup.map_injective (f := K.subtype) Subtype.val_injective
    rw [hmap, Subgroup.map_top, Subgroup.subtype_range]

theorem solvable_strong_embedding_odd_centralizer_supplement
    [Group.IsSolvable G] (H : Subgroup G) (hH : fusionStronglyEmbedded H)
    (z : G) (hzH : z ∈ H) (hz : orderOf z = 2) :
    ∃ X : Subgroup G, X ≤ H ∧ Odd (Nat.card X) ∧ (X.subgroupOf H).Normal ∧
      (H : Set G) = (X : Set G) *
        (H ⊓ Subgroup.centralizer ({z} : Set G) : Set G) ∧
      ¬ Subgroup.normalizer (X : Set G) ≤ H := by
  obtain ⟨K, hHK, hmax⟩ := invertedHull_exists_immediate_overgroup H hH.1
  let HK := H.subgroupOf K
  have hHKstrong : CFSG.OrderReductions.InvolutionGraph.StronglyEmbedded HK :=
    CFSG.OrderReductions.StrongEmbeddingInheritance.intersection_stronglyEmbedded
      H (fusionStronglyEmbedded_to_orderReduction H hH) K hHK.not_ge
      (by simpa only [inf_eq_left.mpr hHK.le] using hH.2.1)
  let zK : K := ⟨z, hHK.le hzH⟩
  have hzK : orderOf zK = 2 := (Subgroup.orderOf_coe zK).symm.trans hz
  have hzHK : zK ∈ HK := hzH
  let R := HK.normalCore
  let X := R.map K.subtype
  have hXK : X ≤ K := Subgroup.map_subtype_le R
  have hXH : X ≤ H := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := hx
    exact HK.normalCore_le hr
  have hXsub : X.subgroupOf K = R :=
    Subgroup.comap_map_eq_self_of_injective Subtype.val_injective R
  have hXnormalK : (X.subgroupOf K).Normal := by rw [hXsub]; infer_instance
  have hKnorm : K ≤ Subgroup.normalizer (X : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXK).mp hXnormalK
  have hXnormalH : (X.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXH).mpr (hHK.le.trans hKnorm)
  have hRodd := CFSG.OrderReductions.StrongEmbedding.normalCore_odd HK hHKstrong
  have hXodd : Odd (Nat.card X) := by
    rw [Subgroup.card_map_of_injective Subtype.val_injective]
    exact hRodd
  have hproduct := invertedHull_maximal_solvable_core_product HK hHKstrong hmax zK hzK hzHK
  refine ⟨X, hXH, hXodd, hXnormalH, ?_, fun hn => hHK.not_ge (hKnorm.trans hn)⟩
  ext h
  constructor
  · intro hh
    have hhK : (⟨h, hHK.le hh⟩ : K) ∈ (HK : Set K) := hh
    rw [hproduct] at hhK
    obtain ⟨r, hr, c, hc, heq⟩ := hhK
    refine Set.mem_mul.mpr ⟨r, Subgroup.mem_map_of_mem K.subtype hr, c,
      ⟨hc.1, ?_⟩, congrArg Subtype.val heq⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hc.2))
  · rintro ⟨x, hx, c, hc, rfl⟩
    exact H.mul_mem (hXH hx) hc.1

end CFSG.ShultStronglyClosedTI
