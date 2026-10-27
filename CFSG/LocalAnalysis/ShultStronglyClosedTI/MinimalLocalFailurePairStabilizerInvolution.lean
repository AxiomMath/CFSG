module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixed
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureCyclicRoot
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.PairInvolutionFixedFieldOrbit

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.ProperPairModel

open CFSG.Open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ShultStronglyClosedTI.CyclicPair

variable {G : Type} [Group G] [Finite G]

theorem proper_pair_stabilizer_exists_involution
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤) :
    ∃ u ∈ pairPointStabilizer H beta, orderOf u = 2 := by
  obtain ⟨hsimple, -⟩ := minimalLocalFailure_nonabelian_simple h
  have hz1 : z ≠ 1 := (orderOf_eq_prime_iff.mp h.local_datum.distinguished_order).2
  have htop : involutionPointHull z = ⊤ := by
    rcases (minimalLocalFailure_hull_normal z).eq_bot_or_eq_top with hbot | htop
    · exact absurd (Subgroup.mem_bot.mp (hbot ▸ localPointHull_distinguished_mem z)) hz1
    · exact htop
  have hnotSE : ¬ fusionStronglyEmbedded H := by
    intro hSE
    apply h.failure
    rw [htop]
    have hmap := hSE.map_mulEquiv (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).symm
    have himage : H.map (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).symm.toMonoidHom =
        H.subgroupOf ⊤ := by
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨x, hx, Subtype.ext rfl⟩
    rwa [himage] at hmap
  have hHeven : Even (Nat.card H) := by
    rw [even_iff_two_dvd, ← h.local_datum.distinguished_order]
    exact Subgroup.orderOf_dvd_natCard H h.local_datum.distinguished_mem
  obtain ⟨g, hgH, hgodd⟩ : ∃ g : G, g ∉ H ∧
      ¬ Odd (Nat.card ↥(H ⊓ H.map (MulAut.conj g⁻¹).toMonoidHom)) := by
    by_contra hall
    push Not at hall
    exact hnotSE ⟨h.local_datum.proper, hHeven, hall⟩
  have heven : 2 ∣ Nat.card ↥(H ⊓ H.map (MulAut.conj g⁻¹).toMonoidHom) :=
    even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hgodd)
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := ↥(H ⊓ H.map (MulAut.conj g⁻¹).toMonoidHom))
    2 heven
  have hvord : orderOf (v : G) = 2 := (Subgroup.orderOf_coe v).trans hv
  have hvH : (v : G) ∈ H := v.2.1
  obtain ⟨w, hwH, hwv⟩ := Subgroup.mem_map.mp v.2.2
  have hvα : rightCosetTranslate H (rightCosetMk H 1) v = rightCosetMk H 1 :=
    (PairInvolutionFixedField.translate_base_iff H v).mpr hvH
  have hvαg : rightCosetTranslate H (rightCosetMk H g) v = rightCosetMk H g := by
    rw [PairInvolutionFixedField.translate_mk_fixed_iff, ← hwv]
    have h1 : g * ((MulAut.conj g⁻¹).toMonoidHom w) * g⁻¹ = w := by
      simp
      group
    rw [h1]
    exact hwH
  have hαg : rightCosetMk H g ≠ rightCosetMk H 1 := by
    intro heq
    apply hgH
    have h1 := (PairInvolutionFixedField.rightCosetMk_eq_iff H g 1).mp heq
    simpa using H.inv_mem h1
  obtain ⟨hQH, -, hQnormal, -, hQp, hQ4, hzQ⟩ := proper_pair_point_root h hcomm hbeta ht hproper
  obtain ⟨hQclass, -, -⟩ := proper_pair_point_root_classes h hcomm hbeta ht hproper
  have hclass : 1 < Nat.card (conjugacyWithin H z) := by
    rw [← hQclass, PairInvolutionFixedField.card_diff_one]
    omega
  obtain ⟨S, hzS, hzcenter⟩ := h.central_sylow
  have htwo := (CFSG.ProperTwoGeneratedCore.local_involution_point_normal_two_hull_sylow_fixed_points
    h.local_datum S hzS
    hzcenter hQH hQnormal hQp hzQ).2.2 hclass
  obtain ⟨x, hxα, hxβ⟩ := htwo (rightCosetMk H 1) (rightCosetMk H g) (rightCosetMk H 1) beta
    hαg.symm hbeta.symm
  rw [pointRightCosetMul_eq_translate] at hxα hxβ
  have hxH : x ∈ H := (PairInvolutionFixedField.translate_base_iff H x).mp hxα
  have hxinvα : rightCosetTranslate H (rightCosetMk H 1) x⁻¹ = rightCosetMk H 1 :=
    (PairInvolutionFixedField.translate_base_iff H x⁻¹).mpr (H.inv_mem hxH)
  have hβx : rightCosetTranslate H beta x⁻¹ = rightCosetMk H g := by
    rw [← hxβ, rightCosetTranslate_mul, mul_inv_cancel, rightCosetTranslate_one]
  refine ⟨x⁻¹ * v * x, ?_, ?_⟩
  · change x⁻¹ * v * x ∈ rightCosetStabilizer H (rightCosetMk H 1) ⊓ rightCosetStabilizer H beta
    refine ⟨?_, ?_⟩
    · show x⁻¹ * v * x ∈ rightCosetStabilizer H (rightCosetMk H 1)
      rw [mem_rightCosetStabilizer_iff, ← rightCosetTranslate_mul, ← rightCosetTranslate_mul,
        hxinvα, hvα, hxα]
    · show x⁻¹ * v * x ∈ rightCosetStabilizer H beta
      rw [mem_rightCosetStabilizer_iff, ← rightCosetTranslate_mul, ← rightCosetTranslate_mul,
        hβx, hvαg, hxβ]
  · rw [show x⁻¹ * (v : G) * x = MulAut.conj x⁻¹ (v : G) by simp,
      MulEquiv.orderOf_eq]
    exact hvord

end CFSG.ShultStronglyClosedTI.ProperPairModel
