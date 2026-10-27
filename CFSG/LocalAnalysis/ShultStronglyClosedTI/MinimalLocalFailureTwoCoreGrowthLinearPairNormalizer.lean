module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureCyclicRoot

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.TwoCoreGrowth

open CFSG.Open CFSG.BenderSuzuki
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.BenderSuzuki.PFAppendixIII

universe u

variable {G : Type u} [Group G]

theorem right_commutator_normalized_by_subgroup (t : G) (J : Subgroup G) :
    J ≤ Subgroup.normalizer (rightInvolutionCommutatorSubgroup t J : Set G) := by
  apply Subgroup.le_normalizer_closure_iff.mpr
  intro g hg x hx
  obtain ⟨j, rfl⟩ := hx
  let X := rightInvolutionCommutatorSubgroup t J
  have hfirst : t⁻¹ * ((j : G) * g⁻¹)⁻¹ * t * ((j : G) * g⁻¹) ∈ X :=
    Subgroup.subset_closure ⟨⟨(j : G) * g⁻¹, J.mul_mem j.property (J.inv_mem hg)⟩, rfl⟩
  have hsecond : t⁻¹ * (g⁻¹)⁻¹ * t * g⁻¹ ∈ X :=
    Subgroup.subset_closure ⟨⟨g⁻¹, J.inv_mem hg⟩, rfl⟩
  have heq : g * (t⁻¹ * (j : G)⁻¹ * t * j) * g⁻¹ =
      (t⁻¹ * (g⁻¹)⁻¹ * t * g⁻¹)⁻¹ *
        (t⁻¹ * ((j : G) * g⁻¹)⁻¹ * t * ((j : G) * g⁻¹)) := by
    group
  rw [heq]
  exact X.mul_mem (X.inv_mem hsecond) hfirst

theorem right_commutator_normalized_by_centralizer (t : G) (J : Subgroup G) :
    Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.normalizer (J : Set G) ≤
      Subgroup.normalizer (rightInvolutionCommutatorSubgroup t J : Set G) := by
  apply Subgroup.le_normalizer_closure_iff.mpr
  intro g hg x hx
  obtain ⟨j, rfl⟩ := hx
  have hj : g * (j : G) * g⁻¹ ∈ J :=
    (Subgroup.mem_normalizer_iff.mp hg.2 j).mp j.property
  have hgt : g * t = t * g := Subgroup.mem_centralizer_singleton_iff.mp hg.1
  have hconj : g * t * g⁻¹ = t := by rw [hgt, mul_assoc, mul_inv_cancel, mul_one]
  have hinv : g * t⁻¹ * g⁻¹ = t⁻¹ := by
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using congrArg Inv.inv hconj
  have heq : g * (t⁻¹ * (j : G)⁻¹ * t * j) * g⁻¹ =
      t⁻¹ * (g * (j : G) * g⁻¹)⁻¹ * t * (g * (j : G) * g⁻¹) := by
    calc
      _ = (g * t⁻¹ * g⁻¹) * (g * (j : G) * g⁻¹)⁻¹ *
          (g * t * g⁻¹) * (g * (j : G) * g⁻¹) := by group
      _ = _ := by rw [hconj, hinv]
  rw [heq]
  exact Subgroup.subset_closure ⟨⟨g * (j : G) * g⁻¹, hj⟩, rfl⟩

variable [Finite G]

theorem original_pair_commutator_normal
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta) :
    let B := pairPointStabilizer H beta
    let X := rightInvolutionCommutatorSubgroup t (pairOddCore H beta)
    B ≤ Subgroup.normalizer (X : Set G) ∧ (X.subgroupOf B).Normal := by
  let B := pairPointStabilizer H beta
  let J := pairOddCore H beta
  let X := rightInvolutionCommutatorSubgroup t J
  obtain ⟨S, hzS, hzcenter⟩ := h.central_sylow
  have hXB : X ≤ B :=
    (pair_commutator_le_odd_core h.local_datum S hzS hzcenter hbeta ht).1.trans
      (pairOddCore_le H beta t).1
  have hBJ : B ≤ Subgroup.normalizer (J : Set G) := by
    intro b hb
    exact minimalLocalFailurePairAction_normalizer_preserves_oddCore B
      ((Subgroup.le_normalizer : B ≤ Subgroup.normalizer (B : Set G)) hb)
  have hBN : B ≤ Subgroup.normalizer (X : Set G) := by
    intro b hb
    obtain ⟨c, hc, j, hj, heq⟩ :=
      (pair_flip_zStar_factorization h.local_datum S hzS hzcenter hbeta ht).2 b
        (pairPointStabilizer_le_pairFlipGroup H beta t hb)
    have hcB : c ∈ B := by
      have hprod : c * j ∈ B := heq ▸ hb
      exact (B.mul_mem_cancel_right ((pairOddCore_le H beta t).1 hj)).mp hprod
    have hcN : c ∈ Subgroup.normalizer (X : Set G) :=
      right_commutator_normalized_by_centralizer t J ⟨hc.2, hBJ hcB⟩
    have hjN : j ∈ Subgroup.normalizer (X : Set G) :=
      right_commutator_normalized_by_subgroup t J hj
    rw [heq]
    exact (Subgroup.normalizer (X : Set G)).mul_mem hcN hjN
  exact ⟨hBN, (Subgroup.normal_subgroupOf_iff_le_normalizer hXB).mpr hBN⟩

theorem original_pair_hull_normalized
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤) :
    pairPointStabilizer H beta ≤
      Subgroup.normalizer (minimalLocalFailureProperPairHull H z beta t : Set G) := by
  let B := pairPointStabilizer H beta
  let X := rightInvolutionCommutatorSubgroup t (pairOddCore H beta)
  let K := minimalLocalFailureProperPairHull H z beta t
  let Q := minimalLocalFailurePairActionPointHull H z
  obtain ⟨hQH, hQK, hQnormal, _, _, _, hzQ⟩ :=
    CyclicPair.proper_pair_point_root h hcomm hbeta ht hproper
  have hHQ : H ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQH).mp hQnormal
  have hBX : B ≤ Subgroup.normalizer (X : Set G) :=
    (original_pair_commutator_normal h hbeta ht).1
  have hXK : X ≤ K := by
    intro x hx
    exact Subgroup.subset_closure (Or.inr hx)
  obtain ⟨S, hzS, hzcenter⟩ := h.central_sylow
  have hflipK : rightPairFlipFiber H z beta ⊆ (K : Set G) := by
    intro s hs
    have hsclass := pair_flips_mem_internal_class h.local_datum S hzS hzcenter hbeta ht hs
    rw [← minimalLocalFailureProperPairHull_eq_native] at hsclass
    obtain ⟨k, rfl⟩ := hsclass
    exact K.mul_mem (K.mul_mem (K.inv_mem k.property)
      (minimalLocalFailureProperPair_distinguished_mem H z beta t)) k.property
  apply Subgroup.le_normalizer_closure_iff.mpr
  intro b hb x hx
  rcases hx with hx | hx
  · rcases Set.mem_insert_iff.mp hx with hxz | hx
    · rw [hxz]
      exact hQK ((Subgroup.mem_normalizer_iff.mp
        (hHQ (pairPointStabilizer_le_point H beta hb)) z).mp hzQ)
    · have hxt : x = t := Set.mem_singleton_iff.mp hx
      rw [hxt]
      have hs := pair_group_conjugate_flip_mem h.local_datum.distinguished_order hbeta ht ht
        (pairPointStabilizer_le_pairFlipGroup H beta t (B.inv_mem hb))
      change b * t * b⁻¹ ∈ K
      simpa only [SetLike.mem_coe, rightConjugateElem, inv_inv] using hflipK hs
  · exact hXK ((Subgroup.mem_normalizer_iff.mp (hBX hb) x).mp hx)

end CFSG.ShultStronglyClosedTI.TwoCoreGrowth
