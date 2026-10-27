module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Rows
import CFSG.HardMathSupport.Dickson.Bal207.SpFCField
import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThreeSU
import CFSG.Adapters.LieModelSmallOrders
import CFSG.HardMathSupport.Dickson.Bal207.LocalBalClassicalSpCent
import CFSG.RankThree.PartOne.KC.OrthogonalSelfDualBlock

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Open
open CFSG.Open.StatedAPI
open CFSG.Blueprint (LieModel)
open Polynomial Matrix Module
open CFSG.HardMathSupport.Dickson.Bal207
open CFSG.HardMathSupport.Dickson.Bal207.FirstClaim
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
open scoped commutatorElement

private noncomputable def k328r7s_M (F : Type) [Field F] : Matrix (Fin 2) (Fin 2) F := !![0, 1; 1, 1]

private theorem k328r7s_dim (F : Type) [Field F] :
    (AdjoinRoot.powerBasis (W2.monic_cyc3' F).ne_zero).dim = 2 := by
  rw [AdjoinRoot.powerBasis_dim, W2.natDegree_cyc3']

private noncomputable def k328r7s_b (F : Type) [Field F] :
    Basis (Fin 2) F (AdjoinRoot (W2.cyc3' F)) :=
  (AdjoinRoot.powerBasis (W2.monic_cyc3' F).ne_zero).basis.reindex
    (finCongr (k328r7s_dim F))

private theorem k328r7s_b_zero (F : Type) [Field F] : k328r7s_b F 0 = 1 := by
  rw [k328r7s_b, Basis.reindex_apply, PowerBasis.basis_eq_pow]
  have h : (((finCongr (k328r7s_dim F)).symm (0 : Fin 2)) : ℕ) = 0 := rfl
  rw [h]; simp

private theorem k328r7s_b_one (F : Type) [Field F] :
    k328r7s_b F 1 = AdjoinRoot.root (W2.cyc3' F) := by
  rw [k328r7s_b, Basis.reindex_apply, PowerBasis.basis_eq_pow]
  have h : (((finCongr (k328r7s_dim F)).symm (1 : Fin 2)) : ℕ) = 1 := rfl
  rw [h]; simp

private theorem k328r7s_root_sq (F : Type) [Field F] [CharP F 2] :
    (AdjoinRoot.root (W2.cyc3' F)) ^ 2 = AdjoinRoot.root (W2.cyc3' F) + 1 := by
  have h : (X ^ 2 + X + 1 : F[X]).eval₂ (AdjoinRoot.of (W2.cyc3' F))
      (AdjoinRoot.root (W2.cyc3' F)) = 0 := AdjoinRoot.eval₂_root (W2.cyc3' F)
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_one] at h
  have h' : (AdjoinRoot.root (W2.cyc3' F)) ^ 2 +
      (AdjoinRoot.root (W2.cyc3' F) + 1) = 0 := by
    rw [← add_assoc]; exact h
  have h'' : (AdjoinRoot.root (W2.cyc3' F)) ^ 2 =
      -(AdjoinRoot.root (W2.cyc3' F) + 1) := (eq_neg_iff_add_eq_zero).mpr h'
  have h2A : (2 : AdjoinRoot (W2.cyc3' F)) = 0 := by
    rw [show (2 : AdjoinRoot (W2.cyc3' F)) = algebraMap F _ 2 by rw [map_ofNat]]
    rw [show (2 : F) = 0 from CharP.cast_eq_zero F 2, map_zero]
  have hneg : -(AdjoinRoot.root (W2.cyc3' F) + 1) =
      AdjoinRoot.root (W2.cyc3' F) + 1 := by
    rw [neg_eq_iff_add_eq_zero, ← two_mul, h2A, zero_mul]
  rw [h'', hneg]

private theorem k328r7s_root_mul (F : Type) [Field F] [CharP F 2] :
    AdjoinRoot.root (W2.cyc3' F) * AdjoinRoot.root (W2.cyc3' F) =
      AdjoinRoot.root (W2.cyc3' F) + 1 := by
  rw [← pow_two, k328r7s_root_sq F]

private theorem k328r7s_repr_one (F : Type) [Field F] :
    (k328r7s_b F).repr (1 : AdjoinRoot (W2.cyc3' F)) = Finsupp.single 0 1 := by
  rw [← k328r7s_b_zero F, Basis.repr_self]

private theorem k328r7s_repr_root (F : Type) [Field F] :
    (k328r7s_b F).repr (AdjoinRoot.root (W2.cyc3' F)) = Finsupp.single 1 1 := by
  rw [← k328r7s_b_one F, Basis.repr_self]

private noncomputable def k328r7s_phiA (F : Type) [Field F] :
    AdjoinRoot (W2.cyc3' F) →ₐ[F] Matrix (Fin 2) (Fin 2) F :=
  (LinearMap.toMatrixAlgEquiv (k328r7s_b F)).toAlgHom.comp
    (Algebra.lsmul F F (AdjoinRoot (W2.cyc3' F)))

private theorem k328r7s_phiA_apply (F : Type) [Field F] (z : AdjoinRoot (W2.cyc3' F)) :
    k328r7s_phiA F z = (LinearMap.toMatrixAlgEquiv (k328r7s_b F))
      (Algebra.lsmul F F (AdjoinRoot (W2.cyc3' F)) z) := by
  rw [k328r7s_phiA, AlgHom.comp_apply]; rfl

private theorem k328r7s_phiA_root (F : Type) [Field F] [CharP F 2] :
    k328r7s_phiA F (AdjoinRoot.root (W2.cyc3' F)) = k328r7s_M F := by
  ext i j
  rw [k328r7s_phiA_apply, LinearMap.toMatrixAlgEquiv_apply, Algebra.lsmul_coe]
  fin_cases i <;> fin_cases j <;>
    simp only [k328r7s_b_zero, k328r7s_b_one, smul_eq_mul, mul_one, k328r7s_repr_one,
      k328r7s_repr_root, k328r7s_root_mul, map_add, Finsupp.add_apply,
      Finsupp.single_eq_same, k328r7s_M, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.empty_val',
      Fin.zero_eta, Fin.mk_one, Fin.isValue]
  all_goals simp

private noncomputable def k328r7s_c0 (F : Type) [Field F] : AdjoinRoot (W2.cyc3' F) →ₗ[F] F :=
  (Finsupp.lapply (0 : Fin 2) : (Fin 2 →₀ F) →ₗ[F] F).comp
    ((k328r7s_b F).repr : AdjoinRoot (W2.cyc3' F) →ₗ[F] (Fin 2 →₀ F))

private noncomputable def k328r7s_c1 (F : Type) [Field F] : AdjoinRoot (W2.cyc3' F) →ₗ[F] F :=
  (Finsupp.lapply (1 : Fin 2) : (Fin 2 →₀ F) →ₗ[F] F).comp
    ((k328r7s_b F).repr : AdjoinRoot (W2.cyc3' F) →ₗ[F] (Fin 2 →₀ F))

private theorem k328r7s_c0_apply (F : Type) [Field F] (z : AdjoinRoot (W2.cyc3' F)) :
    k328r7s_c0 F z = (k328r7s_b F).repr z 0 := by
  simp [k328r7s_c0, Finsupp.lapply_apply]

private theorem k328r7s_c1_apply (F : Type) [Field F] (z : AdjoinRoot (W2.cyc3' F)) :
    k328r7s_c1 F z = (k328r7s_b F).repr z 1 := by
  simp [k328r7s_c1, Finsupp.lapply_apply]

private theorem k328r7s_c0_one (F : Type) [Field F] :
    k328r7s_c0 F (1 : AdjoinRoot (W2.cyc3' F)) = 1 := by
  rw [k328r7s_c0_apply, k328r7s_repr_one, Finsupp.single_eq_same]

private theorem k328r7s_c1_one (F : Type) [Field F] :
    k328r7s_c1 F (1 : AdjoinRoot (W2.cyc3' F)) = 0 := by
  rw [k328r7s_c1_apply, k328r7s_repr_one, Finsupp.single_eq_of_ne (by decide)]

private theorem k328r7s_c0_zero (F : Type) [Field F] :
    k328r7s_c0 F (0 : AdjoinRoot (W2.cyc3' F)) = 0 := map_zero _

private theorem k328r7s_c1_zero (F : Type) [Field F] :
    k328r7s_c1 F (0 : AdjoinRoot (W2.cyc3' F)) = 0 := map_zero _

private theorem k328r7s_phiA_one (F : Type) [Field F] :
    k328r7s_phiA F 1 = 1 := map_one _

private theorem k328r7s_phiA_form (F : Type) [Field F] [CharP F 2]
    (z : AdjoinRoot (W2.cyc3' F)) :
    k328r7s_phiA F z = !![k328r7s_c0 F z, k328r7s_c1 F z; k328r7s_c1 F z,
      k328r7s_c0 F z + k328r7s_c1 F z] := by
  have hsum := (k328r7s_b F).sum_repr z
  rw [Fin.sum_univ_two, k328r7s_b_zero, k328r7s_b_one] at hsum
  rw [← k328r7s_c0_apply, ← k328r7s_c1_apply] at hsum
  have hz : z = k328r7s_c0 F z • (1 : AdjoinRoot (W2.cyc3' F)) +
      k328r7s_c1 F z • AdjoinRoot.root (W2.cyc3' F) := hsum.symm
  conv_lhs => rw [hz]
  rw [map_add, map_smul, map_smul, k328r7s_phiA_one, k328r7s_phiA_root F]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [k328r7s_M, Matrix.smul_apply, Matrix.add_apply,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Fin.zero_eta,
      Fin.mk_one, Fin.isValue, Matrix.empty_val']

private theorem k328r7s_c0_mul (F : Type) [Field F] [CharP F 2] (z w : AdjoinRoot (W2.cyc3' F)) :
    k328r7s_c0 F (z * w) = k328r7s_c0 F z * k328r7s_c0 F w +
      k328r7s_c1 F z * k328r7s_c1 F w := by
  have h := congrFun (congrFun (show k328r7s_phiA F (z * w) = k328r7s_phiA F z *
      k328r7s_phiA F w from map_mul _ _ _) 0) 0
  rw [k328r7s_phiA_form, k328r7s_phiA_form, k328r7s_phiA_form] at h
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one,
    Fin.isValue, Matrix.empty_val'] at h
  linear_combination h

private theorem k328r7s_c1_mul (F : Type) [Field F] [CharP F 2] (z w : AdjoinRoot (W2.cyc3' F)) :
    k328r7s_c1 F (z * w) = k328r7s_c0 F z * k328r7s_c1 F w +
      k328r7s_c1 F z * k328r7s_c0 F w + k328r7s_c1 F z * k328r7s_c1 F w := by
  have h := congrFun (congrFun (show k328r7s_phiA F (z * w) = k328r7s_phiA F z *
      k328r7s_phiA F w from map_mul _ _ _) 0) 1
  rw [k328r7s_phiA_form, k328r7s_phiA_form, k328r7s_phiA_form] at h
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one,
    Fin.isValue, Matrix.empty_val'] at h
  linear_combination h

private theorem k328r7s_c0_mulMat (F : Type) [Field F] [CharP F 2]
    (A B : Matrix (Fin 3) (Fin 3) (AdjoinRoot (W2.cyc3' F))) :
    (A * B).map (k328r7s_c0 F) = A.map (k328r7s_c0 F) * B.map (k328r7s_c0 F) +
      A.map (k328r7s_c1 F) * B.map (k328r7s_c1 F) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.mul_apply, map_sum,
    k328r7s_c0_mul, Finset.sum_add_distrib]

private theorem k328r7s_c1_mulMat (F : Type) [Field F] [CharP F 2]
    (A B : Matrix (Fin 3) (Fin 3) (AdjoinRoot (W2.cyc3' F))) :
    (A * B).map (k328r7s_c1 F) = A.map (k328r7s_c0 F) * B.map (k328r7s_c1 F) +
      A.map (k328r7s_c1 F) * B.map (k328r7s_c0 F) +
      A.map (k328r7s_c1 F) * B.map (k328r7s_c1 F) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.mul_apply, map_sum,
    k328r7s_c1_mul, Finset.sum_add_distrib]

private noncomputable def k328r7s_rhoMat (F : Type) [Field F] [CharP F 2] :
    Matrix (Fin 3) (Fin 3) (AdjoinRoot (W2.cyc3' F)) →*
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F where
  toFun A := fromBlocks (A.map (k328r7s_c0 F)) (A.map (k328r7s_c1 F))
    (A.map (k328r7s_c1 F)) (A.map (k328r7s_c0 F) + A.map (k328r7s_c1 F))
  map_one' := by
    have h0 : (1 : Matrix (Fin 3) (Fin 3) (AdjoinRoot (W2.cyc3' F))).map (k328r7s_c0 F)
        = 1 := by
      ext i j
      by_cases h : i = j <;> simp [Matrix.one_apply, h, k328r7s_c0_one, k328r7s_c0_zero]
    have h1 : (1 : Matrix (Fin 3) (Fin 3) (AdjoinRoot (W2.cyc3' F))).map (k328r7s_c1 F)
        = 0 := by
      ext i j
      by_cases h : i = j <;> simp [h, k328r7s_c1_one, k328r7s_c1_zero]
    rw [h0, h1, add_zero]
    ext (i | i) (j | j) <;>
      simp [Matrix.one_apply, Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl]
  map_mul' A B := by
    ext (i | i) (j | j) <;>
      simp only [fromBlocks_multiply, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
        fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.add_mul, Matrix.mul_add,
        Matrix.add_apply, k328r7s_c0_mulMat, k328r7s_c1_mulMat]
    all_goals ring_nf

private noncomputable def k328r7s_rho (F : Type) [Field F] [CharP F 2] :
    GL (Fin 3) (AdjoinRoot (W2.cyc3' F)) →* GL (Fin 3 ⊕ Fin 3) F :=
  Units.map (k328r7s_rhoMat F)

private theorem k328r7s_eq_coord (F : Type) [Field F] (z : AdjoinRoot (W2.cyc3' F)) :
    z = algebraMap F (AdjoinRoot (W2.cyc3' F)) (k328r7s_c0 F z) +
      algebraMap F (AdjoinRoot (W2.cyc3' F)) (k328r7s_c1 F z) *
        AdjoinRoot.root (W2.cyc3' F) := by
  have hsum := (k328r7s_b F).sum_repr z
  rw [Fin.sum_univ_two, k328r7s_b_zero, k328r7s_b_one] at hsum
  rw [← k328r7s_c0_apply, ← k328r7s_c1_apply] at hsum
  conv_lhs => rw [← hsum]
  simp only [mul_one, Algebra.smul_def]

private noncomputable def k328r7s_liftMat (F : Type) [Field F]
    (M : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 3) (Fin 3) (AdjoinRoot (W2.cyc3' F)) :=
  M.map (fun a => AdjoinRoot.of (W2.cyc3' F) a)

private theorem k328r7s_decomp (F : Type) [Field F]
    (A : Matrix (Fin 3) (Fin 3) (AdjoinRoot (W2.cyc3' F))) :
    A = k328r7s_liftMat F (A.map (k328r7s_c0 F)) +
      (AdjoinRoot.root (W2.cyc3' F)) • k328r7s_liftMat F (A.map (k328r7s_c1 F)) := by
  ext i j
  have h := k328r7s_eq_coord F (A i j)
  simpa [k328r7s_liftMat, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, mul_comm] using h

private theorem k328r7s_rhoMat_sp_iff (F : Type) [Field F] [CharP F 2]
    (A : Matrix (Fin 3) (Fin 3) (AdjoinRoot (W2.cyc3' F))) :
    (k328r7s_rhoMat F A)ᵀ *
        (fromBlocks 0 1 (-1) 0 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) *
        k328r7s_rhoMat F A =
        (fromBlocks 0 1 (-1) 0 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) ↔
      (A.map (k328r7s_c0 F))ᵀ * (A.map (k328r7s_c1 F)) =
          (A.map (k328r7s_c1 F))ᵀ * (A.map (k328r7s_c0 F)) ∧
        (A.map (k328r7s_c0 F))ᵀ * (A.map (k328r7s_c0 F)) +
            (A.map (k328r7s_c0 F))ᵀ * (A.map (k328r7s_c1 F)) +
          (A.map (k328r7s_c1 F))ᵀ * (A.map (k328r7s_c1 F)) = 1 := by
  have : CharP (Matrix (Fin 3) (Fin 3) F) 2 := inferInstance
  set A0 := A.map (k328r7s_c0 F) with hA0
  set A1 := A.map (k328r7s_c1 F) with hA1
  change (fromBlocks A0 A1 A1 (A0 + A1))ᵀ *
      (fromBlocks 0 1 (-1) 0 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) *
      fromBlocks A0 A1 A1 (A0 + A1) =
      (fromBlocks 0 1 (-1) 0 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) ↔
    A0ᵀ * A1 = A1ᵀ * A0 ∧ A0ᵀ * A0 + A0ᵀ * A1 + A1ᵀ * A1 = 1
  rw [fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj]
  simp only [Matrix.mul_zero, Matrix.mul_one, mul_neg,
    neg_mul, add_zero, zero_add, Matrix.transpose_add, neg_add,
    Matrix.add_mul, Matrix.mul_add]
  constructor
  · rintro ⟨h11, h12, h21, h22⟩
    refine ⟨?_, ?_⟩
    · rw [add_eq_zero_iff_eq_neg, neg_inj] at h11
      exact h11.symm
    · rw [CharTwo.neg_eq] at h12
      rw [← h12]; abel
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [h1, neg_add_cancel]
    · rw [CharTwo.neg_eq, ← h2]; abel
    · have hneg : ∀ M : Matrix (Fin 3) (Fin 3) F, -M = M := fun M => CharTwo.neg_eq M
      rw [← h1, hneg, hneg, hneg, h2]
    · rw [h1]; abel

private theorem k328r7s_charP_L (F : Type) [Field F] [CharP F 2] :
    CharP (AdjoinRoot (W2.cyc3' F)) 2 :=
  charP_of_injective_algebraMap (AdjoinRoot.of.injective_of_degree_ne_zero (by
    rw [Polynomial.degree_eq_natDegree (W2.monic_cyc3' F).ne_zero, W2.natDegree_cyc3']
    norm_num)) 2

private noncomputable def k328r7s_sigma (F : Type) [Field F] [CharP F 2] :
    AdjoinRoot (W2.cyc3' F) →+* AdjoinRoot (W2.cyc3' F) := by
  haveI := k328r7s_charP_L F
  exact iterateFrobenius (AdjoinRoot (W2.cyc3' F)) 2 3

private theorem k328r7s_sigma_apply (F : Type) [Field F] [CharP F 2]
    (z : AdjoinRoot (W2.cyc3' F)) : k328r7s_sigma F z = z ^ 8 := rfl

private theorem k328r7s_pow8_of (F : Type) [Field F] [Fintype F] [CharP F 2]
    (hF : Fintype.card F = 8) (a : F) :
    (algebraMap F (AdjoinRoot (W2.cyc3' F)) a) ^ 8 =
      algebraMap F (AdjoinRoot (W2.cyc3' F)) a := by
  rw [← map_pow, ← hF, FiniteField.pow_card]

private theorem k328r7s_root_quad (F : Type) [Field F] [CharP F 2] :
    (AdjoinRoot.root (W2.cyc3' F)) ^ 2 + AdjoinRoot.root (W2.cyc3' F) + 1 = 0 := by
  have h : (X ^ 2 + X + 1 : F[X]).eval₂ (AdjoinRoot.of (W2.cyc3' F))
      (AdjoinRoot.root (W2.cyc3' F)) = 0 := AdjoinRoot.eval₂_root (W2.cyc3' F)
  simpa only [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_one] using h

private theorem k328r7s_root_cube (F : Type) [Field F] [CharP F 2] :
    (AdjoinRoot.root (W2.cyc3' F)) ^ 3 = 1 := by
  have h := k328r7s_root_quad F
  have : (AdjoinRoot.root (W2.cyc3' F)) ^ 3 - 1 = 0 := by
    rw [show (AdjoinRoot.root (W2.cyc3' F)) ^ 3 - 1 =
      ((AdjoinRoot.root (W2.cyc3' F)) - 1) * ((AdjoinRoot.root (W2.cyc3' F)) ^ 2 +
        AdjoinRoot.root (W2.cyc3' F) + 1) by ring, h, mul_zero]
  exact sub_eq_zero.mp this

private theorem k328r7s_sigma_root (F : Type) [Field F] [CharP F 2] :
    k328r7s_sigma F (AdjoinRoot.root (W2.cyc3' F)) =
      AdjoinRoot.root (W2.cyc3' F) + 1 := by
  rw [k328r7s_sigma_apply, show (8 : ℕ) = 2 + 3 * 2 from rfl, pow_add, pow_mul,
    k328r7s_root_cube F, one_pow, mul_one, k328r7s_root_sq F]

private theorem k328r7s_c0_algebraMap (F : Type) [Field F] (a : F) :
    k328r7s_c0 F (algebraMap F (AdjoinRoot (W2.cyc3' F)) a) = a := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, k328r7s_c0_one, smul_eq_mul, mul_one]

private theorem k328r7s_c1_algebraMap (F : Type) [Field F] (a : F) :
    k328r7s_c1 F (algebraMap F (AdjoinRoot (W2.cyc3' F)) a) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, k328r7s_c1_one, smul_eq_mul, mul_zero]

private theorem k328r7s_c0_root_mul (F : Type) [Field F] (a : F) :
    k328r7s_c0 F ((AdjoinRoot.root (W2.cyc3' F)) *
      algebraMap F (AdjoinRoot (W2.cyc3' F)) a) = 0 := by
  rw [mul_comm, ← Algebra.smul_def, map_smul, k328r7s_c0_apply, k328r7s_repr_root,
    Finsupp.single_eq_of_ne (by decide), smul_zero]

private theorem k328r7s_c1_root_mul (F : Type) [Field F] (a : F) :
    k328r7s_c1 F ((AdjoinRoot.root (W2.cyc3' F)) *
      algebraMap F (AdjoinRoot (W2.cyc3' F)) a) = a := by
  rw [mul_comm, ← Algebra.smul_def, map_smul, k328r7s_c1_apply, k328r7s_repr_root,
    Finsupp.single_eq_same, smul_eq_mul, mul_one]

private theorem k328r7s_c0_mul_root (F : Type) [Field F] (a : F) :
    k328r7s_c0 F (algebraMap F (AdjoinRoot (W2.cyc3' F)) a *
      AdjoinRoot.root (W2.cyc3' F)) = 0 := by
  rw [mul_comm]; exact k328r7s_c0_root_mul F a

private theorem k328r7s_c1_mul_root (F : Type) [Field F] (a : F) :
    k328r7s_c1 F (algebraMap F (AdjoinRoot (W2.cyc3' F)) a *
      AdjoinRoot.root (W2.cyc3' F)) = a := by
  rw [mul_comm]; exact k328r7s_c1_root_mul F a

private theorem k328r7s_map_c0_liftMat (F : Type) [Field F] (M : Matrix (Fin 3) (Fin 3) F) :
    (k328r7s_liftMat F M).map (k328r7s_c0 F) = M := by
  ext i j
  simp only [Matrix.map_apply, k328r7s_liftMat]
  exact k328r7s_c0_algebraMap F (M i j)

private theorem k328r7s_map_c1_liftMat (F : Type) [Field F] (M : Matrix (Fin 3) (Fin 3) F) :
    (k328r7s_liftMat F M).map (k328r7s_c1 F) = 0 := by
  ext i j
  simp only [Matrix.map_apply, k328r7s_liftMat, Matrix.zero_apply]
  exact k328r7s_c1_algebraMap F (M i j)

private theorem k328r7s_map_c0_root_liftMat (F : Type) [Field F] (M : Matrix (Fin 3) (Fin 3) F) :
    ((AdjoinRoot.root (W2.cyc3' F)) • k328r7s_liftMat F M).map (k328r7s_c0 F) = 0 := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, k328r7s_liftMat, Matrix.zero_apply]
  rw [Algebra.smul_def, Algebra.algebraMap_self]
  exact k328r7s_c0_root_mul F (M i j)

private theorem k328r7s_map_c1_root_liftMat (F : Type) [Field F] (M : Matrix (Fin 3) (Fin 3) F) :
    ((AdjoinRoot.root (W2.cyc3' F)) • k328r7s_liftMat F M).map (k328r7s_c1 F) = M := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, k328r7s_liftMat]
  rw [Algebra.smul_def, Algebra.algebraMap_self]
  exact k328r7s_c1_root_mul F (M i j)

private theorem k328r7s_decomp_unique (F : Type) [Field F]
    (X Y : Matrix (Fin 3) (Fin 3) (AdjoinRoot (W2.cyc3' F))) :
    X = Y ↔ X.map (k328r7s_c0 F) = Y.map (k328r7s_c0 F) ∧
      X.map (k328r7s_c1 F) = Y.map (k328r7s_c1 F) := by
  constructor
  · intro h; rw [h]; exact ⟨rfl, rfl⟩
  · rintro ⟨h0, h1⟩
    rw [k328r7s_decomp F X, k328r7s_decomp F Y, h0, h1]

private theorem k328r7s_sigma_algebraMap (F : Type) [Field F] [Fintype F] [CharP F 2]
    (hF : Fintype.card F = 8) (a : F) :
    k328r7s_sigma F (algebraMap F (AdjoinRoot (W2.cyc3' F)) a) =
      algebraMap F (AdjoinRoot (W2.cyc3' F)) a := by
  rw [k328r7s_sigma_apply, k328r7s_pow8_of F hF]

private theorem k328r7s_c0_sigma (F : Type) [Field F] [Fintype F] [CharP F 2]
    (hF : Fintype.card F = 8) (z : AdjoinRoot (W2.cyc3' F)) :
    k328r7s_c0 F (k328r7s_sigma F z) = k328r7s_c0 F z + k328r7s_c1 F z := by
  conv_lhs => rw [k328r7s_eq_coord F z]
  simp only [map_add, map_mul, k328r7s_sigma_algebraMap F hF, k328r7s_sigma_root F,
    mul_add, mul_one, k328r7s_c0_algebraMap, k328r7s_c0_mul_root, zero_add]

private theorem k328r7s_c1_sigma (F : Type) [Field F] [Fintype F] [CharP F 2]
    (hF : Fintype.card F = 8) (z : AdjoinRoot (W2.cyc3' F)) :
    k328r7s_c1 F (k328r7s_sigma F z) = k328r7s_c1 F z := by
  conv_lhs => rw [k328r7s_eq_coord F z]
  simp only [map_add, map_mul, k328r7s_sigma_algebraMap F hF, k328r7s_sigma_root F,
    mul_add, mul_one, k328r7s_c1_algebraMap, k328r7s_c1_mul_root, add_zero, zero_add]

private theorem k328r7s_herm_map_c0 (F : Type) [Field F] [Fintype F] [CharP F 2]
    (hF : Fintype.card F = 8) (A : Matrix (Fin 3) (Fin 3) (AdjoinRoot (W2.cyc3' F))) :
    ((A.map (k328r7s_sigma F))ᵀ * A).map (k328r7s_c0 F) =
      (A.map (k328r7s_c0 F))ᵀ * (A.map (k328r7s_c0 F)) +
      (A.map (k328r7s_c1 F))ᵀ * (A.map (k328r7s_c0 F)) +
      (A.map (k328r7s_c1 F))ᵀ * (A.map (k328r7s_c1 F)) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
    map_sum, k328r7s_c0_mul, k328r7s_c0_sigma F hF, k328r7s_c1_sigma F hF,
    add_mul, Finset.sum_add_distrib]

private theorem k328r7s_herm_map_c1 (F : Type) [Field F] [Fintype F] [CharP F 2]
    (hF : Fintype.card F = 8) (A : Matrix (Fin 3) (Fin 3) (AdjoinRoot (W2.cyc3' F))) :
    ((A.map (k328r7s_sigma F))ᵀ * A).map (k328r7s_c1 F) =
      (A.map (k328r7s_c0 F))ᵀ * (A.map (k328r7s_c1 F)) +
      (A.map (k328r7s_c1 F))ᵀ * (A.map (k328r7s_c0 F)) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
    map_sum, k328r7s_c1_mul, k328r7s_c0_sigma F hF, k328r7s_c1_sigma F hF]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  linear_combination (k328r7s_c1 F (A x i) * k328r7s_c1 F (A x j)) * h2

private theorem k328r7s_map_c0_one (F : Type) [Field F] :
    (1 : Matrix (Fin 3) (Fin 3) (AdjoinRoot (W2.cyc3' F))).map (k328r7s_c0 F) = 1 := by
  ext i j
  by_cases h : i = j <;>
    simp [Matrix.one_apply, h, k328r7s_c0_one, k328r7s_c0_zero]

private theorem k328r7s_map_c1_one (F : Type) [Field F] :
    (1 : Matrix (Fin 3) (Fin 3) (AdjoinRoot (W2.cyc3' F))).map (k328r7s_c1 F) = 0 := by
  ext i j
  by_cases h : i = j <;>
    simp [h, k328r7s_c1_one, k328r7s_c1_zero]

private theorem k328r7s_herm_iff (F : Type) [Field F] [Fintype F] [CharP F 2]
    (hF : Fintype.card F = 8) (A : Matrix (Fin 3) (Fin 3) (AdjoinRoot (W2.cyc3' F))) :
    (A.map (k328r7s_sigma F))ᵀ * A = 1 ↔
      (A.map (k328r7s_c0 F))ᵀ * (A.map (k328r7s_c1 F)) =
          (A.map (k328r7s_c1 F))ᵀ * (A.map (k328r7s_c0 F)) ∧
        (A.map (k328r7s_c0 F))ᵀ * (A.map (k328r7s_c0 F)) +
            (A.map (k328r7s_c1 F))ᵀ * (A.map (k328r7s_c0 F)) +
          (A.map (k328r7s_c1 F))ᵀ * (A.map (k328r7s_c1 F)) = 1 := by
  rw [k328r7s_decomp_unique F ((A.map (k328r7s_sigma F))ᵀ * A) 1]
  rw [k328r7s_herm_map_c0 F hF A, k328r7s_herm_map_c1 F hF A,
    k328r7s_map_c0_one F, k328r7s_map_c1_one F]
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨?_, h0⟩
    have : CharP (Matrix (Fin 3) (Fin 3) F) 2 := inferInstance
    have hneg : ∀ X : Matrix (Fin 3) (Fin 3) F, -X = X := by
      intro X
      rw [neg_eq_iff_add_eq_zero, ← two_mul,
        show (2 : Matrix (Fin 3) (Fin 3) F) = 0 from CharP.cast_eq_zero _ 2, zero_mul]
    have h := h1
    rw [add_eq_zero_iff_eq_neg, hneg] at h
    exact h
  · rintro ⟨h1, h2⟩
    refine ⟨h2, ?_⟩
    rw [h1, ← two_mul, show (2 : Matrix (Fin 3) (Fin 3) F) = 0 from CharP.cast_eq_zero _ 2,
      zero_mul]

private theorem k328r7s_rho_sp_iff (F : Type) [Field F] [Fintype F] [CharP F 2]
    (hF : Fintype.card F = 8) (A : GL (Fin 3) (AdjoinRoot (W2.cyc3' F))) :
    k328r7s_rho F A ∈ StatedSp 3 F ↔
      ((A : Matrix (Fin 3) (Fin 3) (AdjoinRoot (W2.cyc3' F))).map (k328r7s_sigma F))ᵀ *
        (A : Matrix (Fin 3) (Fin 3) (AdjoinRoot (W2.cyc3' F))) = 1 := by
  rw [mem_statedSp_iff]
  rw [show ((k328r7s_rho F A : GL (Fin 3 ⊕ Fin 3) F) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      k328r7s_rhoMat F (A : Matrix (Fin 3) (Fin 3) (AdjoinRoot (W2.cyc3' F))) from
    Units.coe_map _ _]
  rw [k328r7s_rhoMat_sp_iff F (A : Matrix _ _ _), k328r7s_herm_iff F hF (A : Matrix _ _ _)]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rwa [h1] at h2
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rwa [← h1] at h2

private noncomputable def k328r7s_z0 (F : Type) [Field F] :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F := fromBlocks 0 1 1 1

private theorem k328r7s_rhoL_zero_one (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    rhoL F 0 1 = k328r7s_z0 F := by
  unfold rhoL k328r7s_z0
  norm_num

private theorem k328r7s_block_shape (F : Type) [Field F] [CharP F 2]
    (g : GL (Fin 3 ⊕ Fin 3) F)
    (hg : (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) * k328r7s_z0 F =
      k328r7s_z0 F * (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F)) :
    (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      fromBlocks (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F).toBlocks₁₁
        (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F).toBlocks₁₂
        (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F).toBlocks₁₂
        ((g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F).toBlocks₁₁ +
          (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F).toBlocks₁₂) := by
  have h := hg
  rw [k328r7s_z0, ← fromBlocks_toBlocks (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F),
    ← fromBlocks_toBlocks (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F)] at h
  rw [fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj] at h
  obtain ⟨h11, h12, h21, h22⟩ := h
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul,
    zero_add, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂,
    Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂] at h11 h12 h21 h22
  rw [← fromBlocks_toBlocks (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F)]
  simp only [Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂]
  rw [fromBlocks_inj]
  exact ⟨rfl, rfl, h11.symm, h12.symm⟩

private theorem k328r7s_map_c0_add (F : Type) [Field F] (X Y : Matrix (Fin 3) (Fin 3) (AdjoinRoot (W2.cyc3' F))) :
    (X + Y).map (k328r7s_c0 F) = X.map (k328r7s_c0 F) + Y.map (k328r7s_c0 F) := by
  ext i j; simp [Matrix.map_apply]

private theorem k328r7s_map_c1_add (F : Type) [Field F] (X Y : Matrix (Fin 3) (Fin 3) (AdjoinRoot (W2.cyc3' F))) :
    (X + Y).map (k328r7s_c1 F) = X.map (k328r7s_c1 F) + Y.map (k328r7s_c1 F) := by
  ext i j; simp [Matrix.map_apply]

private theorem k328r7s_rhoMat_apply_decomp (F : Type) [Field F] [CharP F 2]
    (A₀ A₁ : Matrix (Fin 3) (Fin 3) F) :
    k328r7s_rhoMat F (k328r7s_liftMat F A₀ +
      (AdjoinRoot.root (W2.cyc3' F)) • k328r7s_liftMat F A₁) =
      fromBlocks A₀ A₁ A₁ (A₀ + A₁) := by
  show fromBlocks ((k328r7s_liftMat F A₀ + _ • k328r7s_liftMat F A₁).map (k328r7s_c0 F))
      ((k328r7s_liftMat F A₀ + _ • k328r7s_liftMat F A₁).map (k328r7s_c1 F))
      ((k328r7s_liftMat F A₀ + _ • k328r7s_liftMat F A₁).map (k328r7s_c1 F))
      ((k328r7s_liftMat F A₀ + _ • k328r7s_liftMat F A₁).map (k328r7s_c0 F) +
        (k328r7s_liftMat F A₀ + _ • k328r7s_liftMat F A₁).map (k328r7s_c1 F)) = _
  rw [k328r7s_map_c0_add, k328r7s_map_c1_add, k328r7s_map_c0_liftMat,
    k328r7s_map_c0_root_liftMat, k328r7s_map_c1_liftMat, k328r7s_map_c1_root_liftMat]
  simp

private theorem k328r7s_rhoMat_injective (F : Type) [Field F] [CharP F 2] :
    Function.Injective (k328r7s_rhoMat F) := by
  intro X Y h
  rw [k328r7s_decomp_unique F X Y]
  constructor
  · have := congrArg (fun M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F => M.toBlocks₁₁) h
    simpa [k328r7s_rhoMat, Matrix.toBlocks_fromBlocks₁₁] using this
  · have := congrArg (fun M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F => M.toBlocks₁₂) h
    simpa [k328r7s_rhoMat, Matrix.toBlocks_fromBlocks₁₂] using this

private theorem k328r7s_rhoMat_one (F : Type) [Field F] [CharP F 2] :
    k328r7s_rhoMat F (1 : Matrix (Fin 3) (Fin 3) (AdjoinRoot (W2.cyc3' F))) = 1 := map_one _

private theorem k328r7s_C_le_image (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
    (z₀ : GL (Fin 3 ⊕ Fin 3) F)
    (hz : (z₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) = k328r7s_z0 F) :
    StatedSp 3 F ⊓ Subgroup.centralizer ({z₀} : Set (GL (Fin 3 ⊕ Fin 3) F)) ≤
      (⊤ : Subgroup (GL (Fin 3) (AdjoinRoot (W2.cyc3' F)))).map (k328r7s_rho F) := by
  intro g hg
  rw [Subgroup.mem_inf] at hg
  obtain ⟨_, hgC⟩ := hg
  have hcomm : (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) * k328r7s_z0 F =
      k328r7s_z0 F * (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) := by
    have h := congrArg (fun u : GL (Fin 3 ⊕ Fin 3) F =>
      (u : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F))
      (Subgroup.mem_centralizer_iff.mp hgC z₀ (Set.mem_singleton z₀))
    rw [Units.val_mul, Units.val_mul, hz] at h
    exact h.symm
  have hshape := k328r7s_block_shape F g hcomm
  have hcomm' : ((g⁻¹ : GL (Fin 3 ⊕ Fin 3) F) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) *
      k328r7s_z0 F = k328r7s_z0 F *
        ((g⁻¹ : GL (Fin 3 ⊕ Fin 3) F) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) := by
    have h := congrArg (fun u : GL (Fin 3 ⊕ Fin 3) F =>
      (u : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F))
      (Subgroup.mem_centralizer_iff.mp ((Subgroup.centralizer ({z₀} : Set _)).inv_mem hgC)
        z₀ (Set.mem_singleton z₀))
    rw [Units.val_mul, Units.val_mul, hz] at h
    exact h.symm
  have hshape' := k328r7s_block_shape F g⁻¹ hcomm'
  let A' : Matrix (Fin 3) (Fin 3) (AdjoinRoot (W2.cyc3' F)) :=
    k328r7s_liftMat F (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F).toBlocks₁₁ +
      (AdjoinRoot.root (W2.cyc3' F)) •
        k328r7s_liftMat F (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F).toBlocks₁₂
  let B' : Matrix (Fin 3) (Fin 3) (AdjoinRoot (W2.cyc3' F)) :=
    k328r7s_liftMat F ((g⁻¹ : GL (Fin 3 ⊕ Fin 3) F) :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F).toBlocks₁₁ +
      (AdjoinRoot.root (W2.cyc3' F)) •
        k328r7s_liftMat F ((g⁻¹ : GL (Fin 3 ⊕ Fin 3) F) :
          Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F).toBlocks₁₂
  have hA' : k328r7s_rhoMat F A' = (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) := by
    rw [hshape]; exact k328r7s_rhoMat_apply_decomp F _ _
  have hB' : k328r7s_rhoMat F B' =
      ((g⁻¹ : GL (Fin 3 ⊕ Fin 3) F) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) := by
    rw [hshape']; exact k328r7s_rhoMat_apply_decomp F _ _
  have hAB : A' * B' = 1 := by
    apply k328r7s_rhoMat_injective F
    rw [map_mul, hA', hB', ← Units.val_mul, mul_inv_cancel, Units.val_one, k328r7s_rhoMat_one]
  have hBA : B' * A' = 1 := by
    apply k328r7s_rhoMat_injective F
    rw [map_mul, hA', hB', ← Units.val_mul, inv_mul_cancel, Units.val_one, k328r7s_rhoMat_one]
  refine Subgroup.mem_map.mpr ⟨⟨A', B', hAB, hBA⟩, Subgroup.mem_top _, ?_⟩
  apply Units.ext
  show k328r7s_rhoMat F A' = (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F)
  exact hA' 

private theorem k328r7s_stdComp_le_Y (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
    [Fact (Irreducible (W2.cyc3' F))]
    (hF : Fintype.card F = 8) (z₀ : GL (Fin 3 ⊕ Fin 3) F)
    (hz : (z₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) = k328r7s_z0 F) :
    stdComp (StatedSp 3 F) z₀ ≤
      (StatedSU 3 8 (AdjoinRoot (W2.cyc3' F))).map (k328r7s_rho F) := by
  rw [stdComp, Subgroup.commutator_le]
  intro g hg h hh
  have hle := k328r7s_C_le_image F z₀ hz
  obtain ⟨A, -, hA⟩ := hle hg
  obtain ⟨B, -, hB⟩ := hle hh
  have hghC : (⁅g, h⁆ : GL (Fin 3 ⊕ Fin 3) F) ∈
      StatedSp 3 F ⊓ Subgroup.centralizer ({z₀} : Set (GL (Fin 3 ⊕ Fin 3) F)) := by
    rw [commutatorElement_def]
    exact (StatedSp 3 F ⊓ Subgroup.centralizer ({z₀} : Set _)).mul_mem
      ((StatedSp 3 F ⊓ Subgroup.centralizer ({z₀} : Set _)).mul_mem
        ((StatedSp 3 F ⊓ Subgroup.centralizer ({z₀} : Set _)).mul_mem hg hh)
        ((StatedSp 3 F ⊓ Subgroup.centralizer ({z₀} : Set _)).inv_mem hg))
      ((StatedSp 3 F ⊓ Subgroup.centralizer ({z₀} : Set _)).inv_mem hh)
  have hcomm : (⁅g, h⁆ : GL (Fin 3 ⊕ Fin 3) F) ∈ StatedSp 3 F := (Subgroup.mem_inf.mp hghC).1
  have hAB : k328r7s_rho F ⁅A, B⁆ = ⁅g, h⁆ := by
    rw [map_commutatorElement (k328r7s_rho F) A B, hA, hB]
  refine Subgroup.mem_map.mpr ⟨⁅A, B⁆, ?_, ?_⟩
  · apply Subgroup.subset_closure
    refine ⟨?_, ?_⟩
    · have hdet : Matrix.GeneralLinearGroup.det ⁅A, B⁆ = 1 := by
        rw [map_commutatorElement (Matrix.GeneralLinearGroup.det) A B,
          commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)]
      show ((⁅A, B⁆ : GL (Fin 3) (AdjoinRoot (W2.cyc3' F))) :
        Matrix (Fin 3) (Fin 3) (AdjoinRoot (W2.cyc3' F))).det = 1
      exact congrArg (fun u : (AdjoinRoot (W2.cyc3' F))ˣ =>
        (u : AdjoinRoot (W2.cyc3' F))) hdet
    · rw [← hAB] at hcomm
      exact (k328r7s_rho_sp_iff F hF ⁅A, B⁆).mp hcomm
  · exact hAB

private theorem k328r7s_card_L (F : Type) [Field F] [Fintype F] [CharP F 2]
    [Fact (Irreducible (W2.cyc3' F))] (hF : Fintype.card F = 8) :
    Nat.card (AdjoinRoot (W2.cyc3' F)) = 64 := by
  rw [show Nat.card (AdjoinRoot (W2.cyc3' F)) = Nat.card F ^ 2 from ?_]
  · rw [Nat.card_eq_fintype_card, hF]; norm_num
  · rw [Module.natCard_eq_pow_finrank (K := F),
      (AdjoinRoot.powerBasis (W2.monic_cyc3' F).ne_zero).finrank,
      AdjoinRoot.powerBasis_dim, W2.natDegree_cyc3']

private theorem k328r7s_rho_injective (F : Type) [Field F] [CharP F 2] :
    Function.Injective (k328r7s_rho F) := by
  intro A B h
  apply Units.ext
  apply k328r7s_rhoMat_injective F
  exact congrArg (fun u : GL (Fin 3 ⊕ Fin 3) F =>
    (u : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F)) h

private theorem k328r7s_card_Y (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
    [Fact (Irreducible (W2.cyc3' F))] (hF : Fintype.card F = 8) :
    Nat.card ((StatedSU 3 8 (AdjoinRoot (W2.cyc3' F))).map (k328r7s_rho F)) = 16547328 := by
  have hsu : Nat.card (StatedSU 3 8 (AdjoinRoot (W2.cyc3' F))) = 16547328 := by
    have h := CFSG.SectionRank.OddCover.card_statedSU_three_of_card_eq_sq
      (K := AdjoinRoot (W2.cyc3' F)) (q := 8)
      (by rw [k328r7s_card_L F hF]; norm_num)
    norm_num at h
    exact h
  rw [Subgroup.card_map_of_injective (k328r7s_rho_injective F), hsu]

private theorem k328r7s_card_pos {K : Type} [Group K] [Finite K] {Z X : Subgroup K}
    (h : Pos K Z X) : Nat.card X = 60480 ∨ Nat.card X = 16547328 := by
  obtain ⟨-, -, -, -, -, hZ, hL⟩ := h
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥X), hZ]
  rcases hL with h | h
  · left
    rw [CFSG.Blueprint.LieModel.card_psl_three_four h]
  · right
    rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_eight
      (h.statedClassicalModel (by decide))]

theorem row7_size (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) (z₀ t₀ : GL (Fin 3 ⊕ Fin 3) F)
    (hz : (z₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) = rhoL F 0 1)
    (ht : (t₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      rhoL F (Matrix.diagonal ![0, 1, 1]) (Matrix.diagonal ![1, 1, 0])) :
    SizeLeaf (StatedSp 3 F) z₀ := by
  have hchar : CharP F 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := 3) (by rw [hF]; norm_num)
  have hfact : Fact (Irreducible (W2.cyc3' F)) :=
    ⟨irreducible_cyc3_eight (by rw [Nat.card_eq_fintype_card, hF])⟩
  have _ht := ht
  intro hz₀ X hX hP
  have hXH : X ≤ StatedSp 3 F := hX.trans (stdComp_le (StatedSp 3 F) z₀)
  have hz' : (z₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) = k328r7s_z0 F := by
    rw [hz, k328r7s_rhoL_zero_one]
  have hcases : Nat.card X = 60480 ∨ Nat.card X = 16547328 := by
    rw [← card_subgroupOf_of_le hXH]
    exact k328r7s_card_pos hP
  have hdvdStd : Nat.card (stdComp (StatedSp 3 F) z₀) ∣ 16547328 := by
    have h := Subgroup.card_dvd_of_le (k328r7s_stdComp_le_Y F hF z₀ hz')
    rwa [k328r7s_card_Y F hF] at h
  have hdvdX : Nat.card X ∣ Nat.card (stdComp (StatedSp 3 F) z₀) :=
    Subgroup.card_dvd_of_le hX
  rcases hcases with h | h
  · exfalso
    rw [h] at hdvdX
    exact (by norm_num : ¬ (60480 : ℕ) ∣ 16547328) (hdvdX.trans hdvdStd)
  · have hdvdStd' : Nat.card (stdComp (StatedSp 3 F) z₀) ∣ Nat.card X := by
      rw [h]; exact hdvdStd
    exact Nat.dvd_antisymm hdvdX hdvdStd'

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
