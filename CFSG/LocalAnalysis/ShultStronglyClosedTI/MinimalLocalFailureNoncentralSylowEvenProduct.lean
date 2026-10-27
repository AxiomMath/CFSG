module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureNoncentralSylowHullAction
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperCommutingImagesQuotient

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime

variable {G : Type*} [Group G] [Finite G]

theorem noncentralSylow_moving_conjugate_even_product
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (p : ℕ) (hp : p.Prime) (hpm : p ∣ Nat.card (conjugacyWithin H z))
    (A : Sylow p (triplePointStabilizer H z beta))
    (hzA : z ∈ Subgroup.normalizer
      (((A : Subgroup (triplePointStabilizer H z beta)).map
        (triplePointStabilizer H z beta).subtype : Subgroup G) : Set G))
    (hWne : ((A : Subgroup (triplePointStabilizer H z beta)).map
      (triplePointStabilizer H z beta).subtype : Subgroup G) ≠ ⊥)
    (x : G) (hxH : x ∈ H)
    (hxN : x ∈ Subgroup.normalizer
      (((A : Subgroup (triplePointStabilizer H z beta)).map
        (triplePointStabilizer H z beta).subtype : Subgroup G) : Set G))
    (hxbeta : pointRightCosetMul H beta x = beta)
    (hxmove : pointRightCosetMul H (pointRightCosetMul H beta z) x ≠
      pointRightCosetMul H beta z) :
    Even (orderOf (z * rightConjugateElem z x)) := by
  let W := (A : Subgroup (triplePointStabilizer H z beta)).map
    (triplePointStabilizer H z beta).subtype
  let N := Subgroup.normalizer (W : Set G)
  let zN : N := ⟨z, hzA⟩
  let L := involutionPointHull zN
  let B := (H.subgroupOf N).subgroupOf L
  let f : L →* G := N.subtype.comp L.subtype
  let zL : L := ⟨zN, localPointHull_distinguished_mem zN⟩
  let xN : N := ⟨x, hxN⟩
  let sN : N := rightConjugateElem zN xN
  let sL : L := ⟨sN, Subgroup.subset_closure ⟨xN, rfl⟩⟩
  let R := CFSG.oddCore L
  let q := QuotientGroup.mk' R
  obtain ⟨_hpodd, _hNproper, _hLnormal, hstrong, hrank, _hdist, hpoints, _htrans⟩ :=
    TripleSylowMaximality.leastFailure_triple_normalizer_hull
      h hcomm beta hbeta p hp hpm A hzA hWne
  have hzNorder : orderOf zN = 2 := by
    rw [← orderOf_injective N.subtype N.subtype_injective zN]
    exact h.local_datum.distinguished_order
  have hsNorder : orderOf sN = 2 :=
    order_two_of_mem_pointClass hzNorder ⟨xN, rfl⟩
  have hzLorder : orderOf zL = 2 := by
    rw [← orderOf_injective L.subtype L.subtype_injective zL]
    exact hzNorder
  have hsLorder : orderOf sL = 2 := by
    rw [← orderOf_injective L.subtype L.subtype_injective sL]
    exact hsNorder
  have hzB : zL ∈ B := h.local_datum.distinguished_mem
  have hsB : sL ∈ B :=
    H.mul_mem (H.mul_mem (H.inv_mem hxH) h.local_datum.distinguished_mem) hxH
  have hRodd : Odd (Nat.card R) := CFSG.ComponentClassification.OddCore.odd_card L
  have hzLI : IsInvolution zL := ⟨(orderOf_eq_prime_iff.mp hzLorder).2,
    (orderOf_eq_prime_iff.mp hzLorder).1⟩
  have hsLI : IsInvolution sL := ⟨(orderOf_eq_prime_iff.mp hsLorder).2,
    (orderOf_eq_prime_iff.mp hsLorder).1⟩
  have hqzI : IsInvolution (q zL) :=
    IsInvolution.quotient_mk_of_odd_kernel R hRodd hzLI
  have hqsI : IsInvolution (q sL) :=
    IsInvolution.quotient_mk_of_odd_kernel R hRodd hsLI
  have hqzorder : orderOf (q zL) = 2 := orderOf_eq_prime_iff.mpr ⟨hqzI.2, hqzI.1⟩
  have hqsorder : orderOf (q sL) = 2 := orderOf_eq_prime_iff.mpr ⟨hqsI.2, hqsI.1⟩
  have hqcomm : Commute (q zL) (q sL) :=
    properCommutingImages_quotient_involutions_commute B
      (native_strong_embedding_of_order_conditions hstrong) hrank (q zL) (q sL)
      (Subgroup.mem_map_of_mem q hzB) hqzorder (Subgroup.mem_map_of_mem q hsB) hqsorder
  have hqne : q zL ≠ q sL := by
    intro heq
    have hker : zL * sL⁻¹ ∈ q.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, heq, mul_inv_cancel]
    rw [QuotientGroup.ker_mk'] at hker
    have hfix := noncentralSylow_triple_normalizer_hull_odd_core_fixes
      h hcomm beta hbeta p hp hpm A hzA hWne beta hpoints.2.1 (zL * sL⁻¹) hker
    change pointRightCosetMul H beta (z * (rightConjugateElem z x)⁻¹) = beta at hfix
    have hsame : pointRightCosetMul H beta z =
        pointRightCosetMul H beta (rightConjugateElem z x) := by
      have hh := congrArg (fun omega =>
        pointRightCosetMul H omega (rightConjugateElem z x)) hfix
      simpa only [pointRightCosetMul_mul, mul_assoc, inv_mul_cancel, mul_one] using hh
    have hxbetainv : pointRightCosetMul H beta x⁻¹ = beta := by
      have hh := congrArg (fun omega => pointRightCosetMul H omega x⁻¹) hxbeta
      simpa only [pointRightCosetMul_mul, mul_inv_cancel, pointRightCosetMul_one]
        using hh.symm
    have hsbetaf : pointRightCosetMul H beta (rightConjugateElem z x) =
        pointRightCosetMul H (pointRightCosetMul H beta z) x := by
      rw [rightConjugateElem, ← pointRightCosetMul_mul, ← pointRightCosetMul_mul,
        hxbetainv]
    exact hxmove (hsbetaf.symm.trans hsame.symm)
  have hprodorder : orderOf (q zL * q sL) = 2 := by
    apply orderOf_eq_prime_iff.mpr
    refine ⟨?_, ?_⟩
    · rw [hqcomm.mul_pow, hqzI.2, hqsI.2, one_mul]
    · intro heq
      have hss : q sL * q sL = 1 := by simpa only [pow_two] using hqsI.2
      exact hqne (mul_right_cancel (heq.trans hss.symm))
  have hdiv : 2 ∣ orderOf (zL * sL) := by
    have hh := orderOf_map_dvd q (zL * sL)
    rwa [map_mul, hprodorder] at hh
  have heven : Even (orderOf (zL * sL)) := even_iff_two_dvd.mpr hdiv
  have hfinj : Function.Injective f := N.subtype_injective.comp L.subtype_injective
  rw [← orderOf_injective f hfinj (zL * sL)] at heven
  exact heven

end CFSG.ShultStronglyClosedTI
