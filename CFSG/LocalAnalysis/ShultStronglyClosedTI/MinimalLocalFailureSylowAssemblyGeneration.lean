module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointTransport

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionTripleSylow
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G]

@[expose] def pointPairOddCore (H : Subgroup G)
    (a b : pointRightCosetSpace H) : Subgroup G :=
  let B : Subgroup G := rightCosetStabilizer H a ⊓ rightCosetStabilizer H b
  (CFSG.oddCore B).map B.subtype

@[expose] def FullPointPairGeneration (H : Subgroup G) (z : G) : Prop :=
  ∀ a b : pointRightCosetSpace H, a ≠ b →
    ∀ u : G, u ∈ involutionPointClass z → pointRightCosetMul H a u = a →
      ∀ t : G, t ∈ involutionPointClass z →
        pointRightCosetMul H a t = b → pointRightCosetMul H b t = a →
          (Subgroup.zpowers u ⊔ Subgroup.zpowers t) ⊔ pointPairOddCore H a b = ⊤

@[expose] def BasePointPairGeneration (H : Subgroup G) (z : G) : Prop :=
  ∀ b : pointRightCosetSpace H, b ≠ rightCosetMk H 1 →
    ∀ t : G, t ∈ rightPairFlipFiber H z b →
      (Subgroup.zpowers z ⊔ Subgroup.zpowers t) ⊔ pairOddCore H b = ⊤

theorem pointPairOddCore_base (H : Subgroup G) (b : pointRightCosetSpace H) :
    pointPairOddCore H (rightCosetMk H 1) b = pairOddCore H b := rfl

theorem pointPairOddCore_map_subgroup (B : Subgroup G) (f : G ≃* G) :
    ((CFSG.oddCore B).map B.subtype).map f.toMonoidHom =
      (CFSG.oddCore (B.map f.toMonoidHom)).map (B.map f.toMonoidHom).subtype := by
  let e := B.equivMapOfInjective f.toMonoidHom f.injective
  have hcore : (CFSG.oddCore B).map e.toMonoidHom =
      CFSG.oddCore (B.map f.toMonoidHom) :=
    CFSG.ComponentClassification.OddCore.equiv_invariant e
  have hhom : f.toMonoidHom.comp B.subtype =
      (B.map f.toMonoidHom).subtype.comp e.toMonoidHom := by
    ext b
    rfl
  rw [Subgroup.map_map, hhom, ← Subgroup.map_map, hcore]

theorem pointPairOddCore_right_translate (H : Subgroup G)
    (a b : pointRightCosetSpace H) (g : G) :
    rightConjugate (pointPairOddCore H a b) g =
      pointPairOddCore H (pointRightCosetMul H a g) (pointRightCosetMul H b g) := by
  let f := MulAut.conj g⁻¹
  let B : Subgroup G := rightCosetStabilizer H a ⊓ rightCosetStabilizer H b
  have hpair : (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b).map
      f.toMonoidHom = rightCosetStabilizer H (pointRightCosetMul H a g) ⊓
        rightCosetStabilizer H (pointRightCosetMul H b g) := by
    rw [Subgroup.map_inf _ _ _ f.injective]
    change rightConjugate (rightCosetStabilizer H a) g ⊓
      rightConjugate (rightCosetStabilizer H b) g = _
    rw [rightCosetStabilizer_right_translate, rightCosetStabilizer_right_translate]
    simp only [pointRightCosetMul_eq_translate]
  change ((CFSG.oddCore B).map B.subtype).map f.toMonoidHom = _
  rw [pointPairOddCore_map_subgroup, hpair]
  rfl

theorem point_pair_generation_action_right_conjugate (H : Subgroup G)
    (a : pointRightCosetSpace H) (x g : G) :
    pointRightCosetMul H (pointRightCosetMul H a g) (rightConjugateElem x g) =
      pointRightCosetMul H (pointRightCosetMul H a x) g := by
  rw [pointRightCosetMul_mul, pointRightCosetMul_mul]
  congr 1
  simp only [rightConjugateElem, mul_assoc, mul_inv_cancel_left]

theorem fullPointPairGeneration_at_class_member {H : Subgroup G} {z z₀ : G}
    (hgen : FullPointPairGeneration H z) (hz₀ : z₀ ∈ involutionPointClass z) :
    FullPointPairGeneration H z₀ := by
  unfold FullPointPairGeneration
  rw [pointClass_eq_of_mem hz₀]
  exact hgen

variable [Finite G]

omit [Finite G] in
theorem fullPointPairGeneration_base {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) (hgen : FullPointPairGeneration H z) :
    BasePointPairGeneration H z := by
  intro b hb t ht
  have hzclass : z ∈ involutionPointClass z := by
    exact ⟨1, by simp only [rightConjugateElem, inv_one, one_mul, mul_one]⟩
  have hzbase : pointRightCosetMul H (rightCosetMk H 1) z = rightCosetMk H 1 :=
    (point_right_base_fixed_iff H z).mpr h.distinguished_mem
  have hfirst : pointRightCosetMul H (rightCosetMk H 1) t = b := by
    rw [pointRightCosetMul_eq_translate]
    exact ht.2
  have hreturn : pointRightCosetMul H b t = rightCosetMk H 1 := by
    rw [pointRightCosetMul_eq_translate]
    exact right_pair_flip_returns h.distinguished_order ht
  simpa only [pointPairOddCore_base] using
    hgen (rightCosetMk H 1) b hb.symm z hzclass hzbase t ht.1 hfirst hreturn

theorem fullPointPairGeneration_of_base {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) (hgen : BasePointPairGeneration H z) :
    FullPointPairGeneration H z := by
  intro a b hab u hu hufix t ht hta _htb
  obtain ⟨g, rfl⟩ := hu
  have hzbase : pointRightCosetMul H (rightCosetMk H 1) z = rightCosetMk H 1 :=
    (point_right_base_fixed_iff H z).mpr h.distinguished_mem
  have hclassfix := ((involution_point_unique_containment_action
    h.distinguished_mem h.distinguished_order).2 h.unique_containment).2.1
  obtain ⟨_, _, huniq⟩ := hclassfix (rightConjugateElem z g) ⟨g, rfl⟩
  have hga : pointRightCosetMul H (rightCosetMk H 1) g = a :=
    (huniq _ (point_right_fixed_conjugate hzbase g)).trans (huniq _ hufix).symm
  have hgaInv : pointRightCosetMul H a g⁻¹ = rightCosetMk H 1 := by
    rw [← hga, pointRightCosetMul_mul, mul_inv_cancel, pointRightCosetMul_one]
  let beta := pointRightCosetMul H b g⁻¹
  have hbetag : pointRightCosetMul H beta g = b := by
    simp only [beta, pointRightCosetMul_mul, inv_mul_cancel, pointRightCosetMul_one]
  have hbeta : beta ≠ rightCosetMk H 1 := by
    intro heq
    have hh := congrArg (fun w => pointRightCosetMul H w g) heq
    rw [hbetag, hga] at hh
    exact hab hh.symm
  let t₀ := rightConjugateElem t g⁻¹
  have ht₀ : t₀ ∈ rightPairFlipFiber H z beta := by
    refine ⟨pointClass_right_conjugate_mem ht g⁻¹, ?_⟩
    rw [← pointRightCosetMul_eq_translate]
    change pointRightCosetMul H (rightCosetMk H 1) (rightConjugateElem t g⁻¹) =
      pointRightCosetMul H b g⁻¹
    rw [← hgaInv, point_pair_generation_action_right_conjugate, hta]
  let f := MulAut.conj g⁻¹
  have hzf : f z = rightConjugateElem z g := by
    simp only [f, MulAut.conj_apply, rightConjugateElem, inv_inv]
  have htf : f t₀ = t := by
    simp only [f, t₀, MulAut.conj_apply, rightConjugateElem, inv_inv, mul_assoc,
      inv_mul_cancel_left, inv_mul_cancel, mul_one]
  have hcore : (pairOddCore H beta).map f.toMonoidHom = pointPairOddCore H a b := by
    change rightConjugate (pairOddCore H beta) g = _
    rw [← pointPairOddCore_base H beta, pointPairOddCore_right_translate, hga, hbetag]
  have hmap := congrArg (Subgroup.map f.toMonoidHom) (hgen beta hbeta t₀ ht₀)
  rw [Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers,
    MonoidHom.map_zpowers, Subgroup.map_top_of_surjective _ f.surjective] at hmap
  change (Subgroup.zpowers (f z) ⊔ Subgroup.zpowers (f t₀)) ⊔
    (pairOddCore H beta).map f.toMonoidHom = ⊤ at hmap
  rw [hzf, htf, hcore] at hmap
  exact hmap

theorem fullPointPairGeneration_iff_base {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) :
    FullPointPairGeneration H z ↔ BasePointPairGeneration H z :=
  ⟨fullPointPairGeneration_base h, fullPointPairGeneration_of_base h⟩

end CFSG.ShultStronglyClosedTI
