module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureStrictThetaGrowthFamily
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalizedIntersectionCorrector
public import CFSG.LocalAnalysis.ComponentClassification.TwoRankTransport
public import CFSG.Adapters.QiuzhenLegacy.Compat.G3.RightConjugate

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.StrictThetaGrowth

open CFSG.BenderSuzuki.PFchapter1section1
open CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionNormalizedIntersection
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime

universe u

variable {G : Type u} [Group G]

theorem right_pair_flip_conjugate_of_pair
    {H : Subgroup G} {z v g : G} {beta : rightCosetSpace H}
    (hv : v ∈ rightPairFlipFiber H z beta)
    (hg : g ∈ pairPointStabilizer H beta) :
    rightConjugateElem v g ∈ rightPairFlipFiber H z beta := by
  constructor
  · obtain ⟨a, rfl⟩ := hv.1
    exact ⟨a * g, (rightConjugateElem_comp z a g).symm⟩
  · have hginv := (pairPointStabilizer H beta).inv_mem hg
    have hbase : rightCosetTranslate H (rightCosetMk H 1) g⁻¹ = rightCosetMk H 1 :=
      (mem_rightCosetStabilizer_iff H _ _).mp hginv.1
    have hbeta : rightCosetTranslate H beta g = beta :=
      (mem_rightCosetStabilizer_iff H _ _).mp hg.2
    calc
      rightCosetTranslate H (rightCosetMk H 1) (rightConjugateElem v g) =
          rightCosetTranslate H
            (rightCosetTranslate H
              (rightCosetTranslate H (rightCosetMk H 1) g⁻¹) v) g := by
        rw [rightCosetTranslate_mul, rightCosetTranslate_mul]
        simp only [rightConjugateElem, mul_assoc]
      _ = beta := by rw [hbase, hv.2, hbeta]

theorem noncentral_subgroup_map_automorphism
    (A : Subgroup G) (s : G) (f : G ≃* G)
    (hnoncentral : ¬ A ≤ Subgroup.centralizer ({s} : Set G)) :
    ¬ A.map f.toMonoidHom ≤ Subgroup.centralizer ({f s} : Set G) := by
  intro hcentral
  apply hnoncentral
  intro a ha
  have hh := Subgroup.mem_centralizer_singleton_iff.mp
    (hcentral (Subgroup.mem_map_of_mem f.toMonoidHom ha))
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  apply f.injective
  simpa only [map_mul, MulEquiv.coe_toMonoidHom] using hh

theorem class_hull_map_automorphism (N : Subgroup G) (s : G) (f : G ≃* G) :
    (Subgroup.closure (conjugacyWithin N s)).map f.toMonoidHom =
      Subgroup.closure (conjugacyWithin (N.map f.toMonoidHom) (f s)) := by
  rw [f.toMonoidHom.map_closure, conjugacyWithin_map_automorphism]
  simp only [MulEquiv.coe_toMonoidHom]

variable [Finite G]

theorem admissible_of_kernel_transfer
    (H : Subgroup G) (z : G) (beta : rightCosetSpace H) (p : ℕ)
    (X A : Subgroup G) (v : G) (hadm : Admissible H z beta p X A v)
    (R N : Subgroup G) (hRne : R ≠ ⊥) (hRJ : R ≤ pairOddCore H beta)
    (hvR : v ∈ Subgroup.normalizer (R : Set G))
    (hAR : A ≤ Subgroup.normalizer (R : Set G))
    (hNR : N ≤ Subgroup.normalizer (R : Set G))
    (w : G) (hw : w ∈ triplePointStabilizer H z beta)
    (hsR : rightConjugateElem z w ∈ Subgroup.normalizer (R : Set G))
    (hsA : rightConjugateElem z w ∈ Subgroup.normalizer (A : Set G))
    (hsnoncentral : ¬ A ≤ Subgroup.centralizer ({rightConjugateElem z w} : Set G))
    (hNs : 2 ≤ CFSG.Open.pRank 2
      (Subgroup.closure (conjugacyWithin N (rightConjugateElem z w)))) :
    Admissible H z beta p (rightConjugate R w⁻¹)
      (rightConjugate A w⁻¹) (rightConjugateElem v w⁻¹) := by
  let g := w⁻¹
  let f := MulAut.conj g⁻¹
  let R1 := rightConjugate R g
  let A1 := rightConjugate A g
  let v1 := rightConjugateElem v g
  let s := rightConjugateElem z w
  have hsback : rightConjugateElem s g = z := by
    dsimp only [s, g, rightConjugateElem]
    group
  have hfs : f s = z := by
    simpa only [f, MulAut.conj_apply, inv_inv, rightConjugateElem] using hsback
  have hgB : g ∈ pairPointStabilizer H beta :=
    (pairPointStabilizer H beta).inv_mem hw.1
  have hJN : pairPointStabilizer H beta ≤
      Subgroup.normalizer (pairOddCore H beta : Set G) := by
    have hJB : pairOddCore H beta ≤ pairPointStabilizer H beta :=
      Subgroup.map_subtype_le _
    have hnormal : ((pairOddCore H beta).subgroupOf
        (pairPointStabilizer H beta)).Normal := by
      change (((CFSG.oddCore (pairPointStabilizer H beta)).map
        (pairPointStabilizer H beta).subtype).comap
          (pairPointStabilizer H beta).subtype).Normal
      rw [Subgroup.comap_map_eq_self_of_injective
        (pairPointStabilizer H beta).subtype_injective]
      infer_instance
    let : ((pairOddCore H beta).subgroupOf
      (pairPointStabilizer H beta)).Normal := hnormal
    exact Subgroup.le_normalizer_of_normal_subgroupOf hJB
  have hJg : rightConjugate (pairOddCore H beta) g = pairOddCore H beta :=
    rightConjugate_eq_self_of_mem_normalizer (hJN hgB)
  have hR1J : R1 ≤ pairOddCore H beta := by
    have hh := Subgroup.map_mono (f := f.toMonoidHom) hRJ
    change R1 ≤ rightConjugate (pairOddCore H beta) g at hh
    rwa [hJg] at hh
  have hA1J : A1 ≤ pairOddCore H beta := by
    have hh := Subgroup.map_mono (f := f.toMonoidHom)
      (hadm.witness_le.trans inf_le_right)
    change A1 ≤ rightConjugate (pairOddCore H beta) g at hh
    rwa [hJg] at hh
  have hR1ne : R1 ≠ ⊥ := by
    intro hbot
    exact hRne ((Subgroup.map_eq_bot_iff_of_injective _ f.injective).mp hbot)
  have hzR1 : z ∈ Subgroup.normalizer (R1 : Set G) := by
    have hh := right_conjugate_mem_normalizer hsR g
    rwa [hsback] at hh
  have hzA1 : z ∈ Subgroup.normalizer (A1 : Set G) := by
    have hh := right_conjugate_mem_normalizer hsA g
    rwa [hsback] at hh
  have hA1noncentral : ¬ A1 ≤ Subgroup.centralizer ({z} : Set G) := by
    have hh := noncentral_subgroup_map_automorphism A s f hsnoncentral
    rwa [hfs] at hh
  have hA1N : A1 ≤ Subgroup.normalizer (R1 : Set G) := by
    rw [show R1 = R.map f.toMonoidHom from rfl,
      ← Subgroup.map_equiv_normalizer_eq R f]
    exact Subgroup.map_mono hAR
  have hNimage : N.map f.toMonoidHom ≤ Subgroup.normalizer (R1 : Set G) := by
    rw [show R1 = R.map f.toMonoidHom from rfl,
      ← Subgroup.map_equiv_normalizer_eq R f]
    exact Subgroup.map_mono hNR
  have hhull : Subgroup.closure (conjugacyWithin (N.map f.toMonoidHom) z) ≤
      Subgroup.closure (conjugacyWithin (Subgroup.normalizer (R1 : Set G)) z) := by
    apply Subgroup.closure_mono
    rintro a ⟨n, rfl⟩
    exact ⟨⟨n.val, hNimage n.property⟩, rfl⟩
  have hrank : 2 ≤ CFSG.Open.pRank 2
      (Subgroup.closure (conjugacyWithin (Subgroup.normalizer (R1 : Set G)) z)) := by
    have hmaprank := CFSG.ComponentClassification.TwoRankTransport.equiv_map
      (Subgroup.closure (conjugacyWithin N s)) f
    rw [class_hull_map_automorphism, hfs] at hmaprank
    exact (hNs.trans_eq hmaprank.symm).trans
      (CFSG.ComponentClassification.TwoRankTransport.mono hhull)
  exact ⟨hR1ne, hR1J.trans
      (Subgroup.map_subtype_le _ |>.trans (pairPointStabilizer_le_point H beta)),
    rightConjugate_eq_self_of_mem_normalizer hzR1,
    right_pair_flip_conjugate_of_pair hadm.flip hgB,
    right_conjugate_mem_normalizer hvR g, hrank, le_inf hA1N hA1J,
    hadm.witness_prime.map f.toMonoidHom,
    rightConjugate_eq_self_of_mem_normalizer hzA1,
    right_conjugate_mem_normalizer hadm.flip_normalizes_witness g, hA1noncentral⟩

end CFSG.ShultStronglyClosedTI.StrictThetaGrowth
