module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailurePairActionQuotient
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionTripleSylowGeometry

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionTripleSylow

universe u

variable {G : Type u} [Group G]

theorem minimalLocalFailurePairAction_normalizer_preserves_oddCore (B : Subgroup G) :
    Subgroup.normalizer (B : Set G) ≤
      Subgroup.normalizer (((oddCore B).map B.subtype : Subgroup G) : Set G) := by
  intro g hg
  let e : B ≃* B := B.normalizerMonoidHom ⟨g, hg⟩
  have hchar := CFSG.ComponentClassification.OddCore.char_invariant e
  change (oddCore B).map e.toMonoidHom = oddCore B at hchar
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  have hhom : (MulAut.conj g : G →* G).comp B.subtype = B.subtype.comp e.toMonoidHom := by
    ext b
    exact (B.normalizerMonoidHom_apply_apply_coe ⟨g, hg⟩ b).symm
  rw [Subgroup.map_map, hhom, ← Subgroup.map_map, hchar]

theorem minimalLocalFailurePairAction_join_normalized_of_commutators
    (P W : Subgroup G) (z : G) (hz : orderOf z = 2)
    (hzW : z ∈ Subgroup.normalizer (W : Set G))
    (hcomm : ∀ p ∈ P, z⁻¹ * p⁻¹ * z * p ∈ W) :
    z ∈ Subgroup.normalizer ((P ⊔ W : Subgroup G) : Set G) := by
  let X := P ⊔ W
  have hzinv : z⁻¹ = z := inv_eq_self_of_orderOf_eq_two hz
  have hconjle : X.map (MulAut.conj z).toMonoidHom ≤ X := by
    rw [Subgroup.map_sup]
    apply sup_le
    · rintro q ⟨p, hp, rfl⟩
      have hc := hcomm p hp
      have hmem : p * (z⁻¹ * p⁻¹ * z * p)⁻¹ ∈ X :=
        X.mul_mem ((show P ≤ X from le_sup_left) hp)
          ((show W ≤ X from le_sup_right) (W.inv_mem hc))
      have heq : p * (z⁻¹ * p⁻¹ * z * p)⁻¹ = z * p * z⁻¹ := by
        calc
          p * (z⁻¹ * p⁻¹ * z * p)⁻¹ = z⁻¹ * p * z := by group
          _ = z * p * z⁻¹ := by rw [hzinv]
      simpa only [heq, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hmem
    · change W.map (MulAut.conj z : G →* G) ≤ X
      rw [Subgroup.mem_normalizer_iff_map_conj_eq.mp hzW]
      exact le_sup_right
  have hconj (x : G) (hx : x ∈ X) : z * x * z⁻¹ ∈ X :=
    hconjle (Subgroup.mem_map_of_mem (MulAut.conj z).toMonoidHom hx)
  apply Subgroup.mem_normalizer_iff.mpr
  intro x
  refine ⟨hconj x, fun hx => ?_⟩
  have heq : z * (z * x * z⁻¹) * z⁻¹ = x := by
    have hzz : z * z = 1 := by
      simpa only [pow_two] using (orderOf_eq_prime_iff.mp hz).1
    rw [hzinv]
    calc
      z * (z * x * z) * z = (z * z) * x * (z * z) := by group
      _ = x := by rw [hzz, one_mul, mul_one]
  simpa only [heq] using hconj _ hx

theorem minimalLocalFailurePairAction_triple_ne_pair [Finite G]
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hWJ : minimalLocalFailureProperPairClassCommutators H z ≤ pairOddCore H beta) :
    triplePointStabilizer H z beta ≠ pairPointStabilizer H beta := by
  intro hEB
  let J := pairOddCore H beta
  let W := minimalLocalFailureProperPairClassCommutators H z
  have hJH : J ≤ H := (pairOddCore_le H beta t).2.2
  have hzB : z ∈ Subgroup.normalizer (pairPointStabilizer H beta : Set G) := by
    rw [← hEB]
    exact triple_stabilizer_normalized_by_distinguished h.local_datum beta
  have hzJ : z ∈ Subgroup.normalizer (J : Set G) :=
    minimalLocalFailurePairAction_normalizer_preserves_oddCore _ hzB
  obtain ⟨S, hzS, hzcenter⟩ := h.central_sylow
  have hfactor := point_subgroup_eq_centralizer_mul_inverted_set
    h.local_datum S hzS hzcenter hbeta ht
  have hproducts : ∀ s ∈ conjugacyWithin H z, z * s ∈ W := by
    rintro s ⟨a, rfl⟩
    have ha : (a : G) ∈ (H : Set G) := a.property
    rw [hfactor] at ha
    obtain ⟨c, hc, i, hi, hci⟩ := Set.mem_mul.mp ha
    have hcconj : c⁻¹ * z * c = z := by
      have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hc
      rw [mul_assoc, ← hcomm, inv_mul_cancel_left]
    have hconj : (a : G)⁻¹ * z * a = i⁻¹ * z * i := by
      rw [← hci, mul_inv_rev]
      calc
        (i⁻¹ * c⁻¹) * z * (c * i) = i⁻¹ * (c⁻¹ * z * c) * i := by group
        _ = i⁻¹ * z * i := by rw [hcconj]
    have hcommW := minimalLocalFailurePairAction_odd_subgroup_commutator_mem
      H h.local_datum.distinguished_mem h.local_datum.distinguished_order
      J hJH (pairOddCore_odd H beta) hzJ hi.1
    rw [hconj]
    simpa only [inv_eq_self_of_orderOf_eq_two h.local_datum.distinguished_order, mul_assoc]
      using hcommW
  obtain ⟨s, hs, hsne, hscomm⟩ := minimalLocalFailure_commuting_class_member h
  have hsambient : s ∈ involutionPointClass z := by
    obtain ⟨a, ha⟩ := hs
    exact ⟨a, ha⟩
  have hsorder := order_two_of_mem_pointClass h.local_datum.distinguished_order hsambient
  have hzsone : z * s = 1 := square_one_eq_one_of_mem_odd_subgroup J
    (pairOddCore_odd H beta) (hWJ (hproducts s hs)) (by
      rw [hscomm.mul_pow, (orderOf_eq_prime_iff.mp h.local_datum.distinguished_order).1,
        (orderOf_eq_prime_iff.mp hsorder).1, mul_one])
  have hsequal : s = z := by
    have hh := mul_eq_one_iff_eq_inv.mp hzsone
    simpa only [inv_eq_self_of_orderOf_eq_two hsorder] using hh.symm
  exact hsne hsequal

end CFSG.ShultStronglyClosedTI
