module

public import CFSG.LocalAnalysis.StandardType.GGQ2OrthBlocksGroup
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.CompPSp
public import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksIdem
public import CFSG.ClassicalGroups.Orthogonal.MatrixIsometry

public section

namespace CFSG.StandardType.GGQ2Frame.OrthBlocks

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.SpJoin
  CFSG.StandardType.ClassicalPosition Matrix
open CFSG.Open (StatedSp)
open scoped commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma orth_blk_isometry {K : Type} [Field K] [CharP K 2] {ι : Type}
    [Fintype ι] [DecidableEq ι] {Q : (ι → K) → K} {B : Matrix ι ι K} {ε A : Matrix ι ι K}
    (hadd : ∀ v w, Q (v + w) = Q v + Q w + v ⬝ᵥ (B *ᵥ w))
    (hεid : IsIdempotentElem ε) (hεtrB : Matrix.transpose ε * B = B * ε)
    (hAε : A * ε = ε * A) (hAiso : ∀ v, Q (A.mulVec v) = Q v) :
    ∀ v, Q ((A * ε + (1 - ε)).mulVec v) = Q v := by
  intro v
  have hε1 : ε * (1 - ε) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hεid.eq, sub_self]
  have hcross0 : ∀ u w : ι → K,
      (ε.mulVec u) ⬝ᵥ (B *ᵥ w) = u ⬝ᵥ (B *ᵥ (ε.mulVec w)) := by
    intro u w
    have h := Matrix.dotProduct_mulVec u (Matrix.transpose ε) (B *ᵥ w)
    rw [Matrix.vecMul_transpose, Matrix.mulVec_mulVec, hεtrB,
      ← Matrix.mulVec_mulVec] at h
    exact h.symm
  have hεεv : ε.mulVec ((1 - ε).mulVec v) = 0 := by
    rw [Matrix.mulVec_mulVec, hε1, Matrix.zero_mulVec]
  have hcrossA : (A.mulVec (ε.mulVec v)) ⬝ᵥ (B *ᵥ ((1 - ε).mulVec v)) = 0 := by
    have hAεv : A.mulVec (ε.mulVec v) = ε.mulVec (A.mulVec v) := by
      rw [Matrix.mulVec_mulVec, hAε, ← Matrix.mulVec_mulVec]
    rw [hAεv, hcross0 (A.mulVec v) ((1 - ε).mulVec v), hεεv, Matrix.mulVec_zero,
      dotProduct_zero]
  have hcrossV : (ε.mulVec v) ⬝ᵥ (B *ᵥ ((1 - ε).mulVec v)) = 0 := by
    rw [hcross0 v ((1 - ε).mulVec v), hεεv, Matrix.mulVec_zero, dotProduct_zero]
  have hXv : (A * ε + (1 - ε)).mulVec v =
      A.mulVec (ε.mulVec v) + (1 - ε).mulVec v := by
    rw [Matrix.add_mulVec, Matrix.mulVec_mulVec]
  have hsplit : v = ε.mulVec v + (1 - ε).mulVec v := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  rw [hXv, hadd, hcrossA, add_zero, hAiso]
  conv_rhs => rw [hsplit]
  rw [hadd, hcrossV, add_zero]

theorem orthIsComponentOfGlBlockCentralizer_holds : OrthIsComponentOfGlBlockCentralizer := by
  intro K _ _ _ t δ S hS J' hJ
  let J : Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
      (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K := Matrix.fromBlocks 0 1 (-1) 0
  have hsym : J * J = -1 := by
    change (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
      (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) * Matrix.fromBlocks 0 1 (-1) 0 = -1
    exact SpBlocks.symJ_mul_self (t + δ.val) (K := K)
  have hJdet : IsUnit J.det :=
    Matrix.isUnit_det_of_left_inverse (B := -J) (by rw [neg_mul, hsym, neg_neg])
  have hQadd : ∀ v w : Fin (t + δ.val) ⊕ Fin (t + δ.val) → K,
      planeQ t δ (v + w) = planeQ t δ v + planeQ t δ w + v ⬝ᵥ (J *ᵥ w) := by
    intro v w
    exact planeQ_add t δ v w
  obtain ⟨ε, hεprim, hcomp⟩ :=
    Block.exists_isPrimStarIdemIn_isComponentOf_glBlockCentralizer
      (j := (omegaQ (K := K) t δ).subtype) (Subgroup.subtype_injective _)
      S hS (formAdj (RingHom.id K) J)
      (Geo.formAdj_one (RingHom.id K) hJdet)
      (fun a _ b _ => Geo.formAdj_add (RingHom.id K) J a b)
      (by
        intro ε hεA hεid hεadj x hx y hy
        change formAdj (RingHom.id K) J ε = ε at hεadj
        have hεtr : Matrix.transpose ε * J = J * ε := by
          have hεadj' : J⁻¹ * Matrix.transpose ε * J = ε := by
            have hmap : ε.map (RingHom.id K) = ε := by
              ext i j
              rfl
            simpa [formAdj, hmap] using hεadj
          have h := congrArg (fun M => J * M) hεadj'
          rw [← Matrix.mul_assoc J (J⁻¹ * Matrix.transpose ε) J,
            ← Matrix.mul_assoc J J⁻¹ (Matrix.transpose ε),
            Matrix.mul_nonsing_inv J hJdet, Matrix.one_mul] at h
          exact h
        have hxS : ((x : ↥(omegaQ (K := K) t δ)) : GL (Fin (t + δ.val) ⊕
            Fin (t + δ.val)) K) ∈ Subgroup.centralizer S := Subgroup.mem_comap.mp hx
        have hyS : ((y : ↥(omegaQ (K := K) t δ)) : GL (Fin (t + δ.val) ⊕
            Fin (t + δ.val)) K) ∈ Subgroup.centralizer S := Subgroup.mem_comap.mp hy
        have hxε : (((x : ↥(omegaQ (K := K) t δ)) : GL (Fin (t + δ.val) ⊕
            Fin (t + δ.val)) K) : Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
            (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) * ε =
            ε * (((x : ↥(omegaQ (K := K) t δ)) : GL (Fin (t + δ.val) ⊕
            Fin (t + δ.val)) K) : Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
            (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) :=
          SpBlocks.commute_of_mem_adjoin hxS hεA
        have hyε : (((y : ↥(omegaQ (K := K) t δ)) : GL (Fin (t + δ.val) ⊕
            Fin (t + δ.val)) K) : Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
            (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) * ε =
            ε * (((y : ↥(omegaQ (K := K) t δ)) : GL (Fin (t + δ.val) ⊕
            Fin (t + δ.val)) K) : Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
            (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) :=
          SpBlocks.commute_of_mem_adjoin hyS hεA
        have hxO : ((x : ↥(omegaQ (K := K) t δ)) : GL (Fin (t + δ.val) ⊕
            Fin (t + δ.val)) K) ∈ LargeEvenOrthGroup (planeQ (K := K) t δ) := by
          refine (Subgroup.commutator_le.mpr fun a ha b hb => ?_) (by
            simpa [omegaQ, largeEvenOmega_def] using x.2)
          rw [commutatorElement_def]
          exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
        have hyO : ((y : ↥(omegaQ (K := K) t δ)) : GL (Fin (t + δ.val) ⊕
            Fin (t + δ.val)) K) ∈ LargeEvenOrthGroup (planeQ (K := K) t δ) := by
          refine (Subgroup.commutator_le.mpr fun a ha b hb => ?_) (by
            simpa [omegaQ, largeEvenOmega_def] using y.2)
          rw [commutatorElement_def]
          exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
        have hxiso := CFSG.PGLModel.mem_orthogonalGroup_iff.mp hxO
        have hyiso := CFSG.PGLModel.mem_orthogonalGroup_iff.mp hyO
        let X : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K :=
          cpSp_blk ((x : ↥(omegaQ (K := K) t δ)) : GL (Fin (t + δ.val) ⊕
            Fin (t + δ.val)) K) ε hεid hxε
        let Y : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K :=
          cpSp_blk ((y : ↥(omegaQ (K := K) t δ)) : GL (Fin (t + δ.val) ⊕
            Fin (t + δ.val)) K) ε hεid hyε
        have hXval : (X : Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
            (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) =
            (((x : ↥(omegaQ (K := K) t δ)) : GL (Fin (t + δ.val) ⊕
            Fin (t + δ.val)) K) : Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
            (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) * ε + (1 - ε) := rfl
        have hYval : (Y : Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
            (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) =
            (((y : ↥(omegaQ (K := K) t δ)) : GL (Fin (t + δ.val) ⊕
            Fin (t + δ.val)) K) : Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
            (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) * ε + (1 - ε) := rfl
        have hXmem : X ∈ LargeEvenOrthGroup (planeQ (K := K) t δ) := by
          rw [CFSG.PGLModel.mem_orthogonalGroup_iff]
          intro v
          rw [hXval]
          exact orth_blk_isometry hQadd hεid hεtr hxε hxiso v
        have hYmem : Y ∈ LargeEvenOrthGroup (planeQ (K := K) t δ) := by
          rw [CFSG.PGLModel.mem_orthogonalGroup_iff]
          intro v
          rw [hYval]
          exact orth_blk_isometry hQadd hεid hεtr hyε hyiso v
        have hwΩ : ⁅Y, X⁆ ∈ omegaQ (K := K) t δ := by
          rw [omegaQ, largeEvenOmega_def]
          exact Subgroup.commutator_mem_commutator hYmem hXmem
        refine ⟨⟨⁅Y, X⁆, hwΩ⟩, ?_⟩
        have hgl : (⁅Y, X⁆ : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) * (X * Y) = Y * X := by
          rw [commutatorElement_def]
          group
        have hcoe := congrArg (fun u : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K =>
          (u : Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
            (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K)) hgl
        simp only [Units.val_mul] at hcoe
        rw [hXval, hYval] at hcoe
        exact hcoe)
      hJ
  refine ⟨ε, ?_, hcomp⟩
  exact (Block.isPrimStarIdemIn_formAdj_iff (RingHom.id K) J
    (Algebra.adjoin K (Units.val '' S)) ε).mp hεprim

end CFSG.StandardType.GGQ2Frame.OrthBlocks
