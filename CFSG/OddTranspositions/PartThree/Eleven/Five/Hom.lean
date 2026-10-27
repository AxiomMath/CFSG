module

public import CFSG.OddTranspositions.PartThree.Eleven.Five.ReflConj
public import CFSG.ClassicalGroups.Orthogonal.FiveSquareFrameGeneration
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.ClassicalGroups.Orthogonal.RootGroupFixedCard
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthConj
public import CFSG.ClassicalInvolution.Orders.OrthogonalIndex
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareEigenspaces
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquarePositive
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.ClassicalGroups.Orthogonal Matrix

@[expose] noncomputable def fiveT : GL (Fin 5) (ZMod 5) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal ![1, 1, 1, 1, 2]) (by
    rw [Matrix.det_diagonal]
    decide)

@[expose] noncomputable def fivePlusMap : GL (Fin 5) (ZMod 5) →* GL (Fin 5) (ZMod 5) where
  toFun g := Matrix.GeneralLinearGroup.scalar (Fin 5) (Matrix.GeneralLinearGroup.det g) *
    (fiveT * g * fiveT⁻¹)
  map_one' := by simp
  map_mul' g h := by
    have hc := Matrix.GeneralLinearGroup.scalar_commute (n := Fin 5)
      (Matrix.GeneralLinearGroup.det h) (fiveT * g * fiveT⁻¹)
    simp only [map_mul]
    calc _ = Matrix.GeneralLinearGroup.scalar (Fin 5) (Matrix.GeneralLinearGroup.det g) *
          (Matrix.GeneralLinearGroup.scalar (Fin 5) (Matrix.GeneralLinearGroup.det h) *
            (fiveT * g * fiveT⁻¹)) * (fiveT * h * fiveT⁻¹) := by group
      _ = _ := by rw [hc]; group

@[expose] noncomputable def fiveGLEquiv :
    GL (Fin 5) (ZMod 5) ≃* ((Fin 5 → ZMod 5) ≃ₗ[ZMod 5] (Fin 5 → ZMod 5)) :=
  Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _)

theorem fiveGLEquiv_apply (g : GL (Fin 5) (ZMod 5)) (x : Fin 5 → ZMod 5) :
    fiveGLEquiv g x = (g : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ x := by
  simp [fiveGLEquiv, Matrix.GeneralLinearGroup.toLin]

namespace FiveHom

theorem Q_T (y : Fin 5 → ZMod 5) :
    FiveSquareFrameGeneration.Q ((fiveT : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ y) =
      fiveForm 4 true y y := by
  have h4 : (4 : ZMod 5) = -1 := by decide
  simp [fiveT, FiveSquareFrameGeneration.Q, FiveSquareFrameGeneration.Generic.Q,
    QuadraticMap.weightedSumSquares_apply,
    fiveForm, Fin.sum_univ_five, Fin.sum_univ_four, Matrix.mulVec, dotProduct,
    Matrix.diagonal]
  ring_nf
  rw [h4]
  rw [show y 4 ^ 2 * (-1 : ZMod 5) = -(y 4 ^ 2) from mul_neg_one _]
  rw [sub_eq_add_neg]
  abel

theorem Q_smul (c : ZMod 5) (y : Fin 5 → ZMod 5) :
    FiveSquareFrameGeneration.Q (c • y) = c ^ 2 * FiveSquareFrameGeneration.Q y := by
  rw [FiveSquareFrameGeneration.Q, FiveSquareFrameGeneration.Generic.Q,
    QuadraticMap.weightedSumSquares_apply, QuadraticMap.weightedSumSquares_apply,
    Fin.sum_univ_five, Fin.sum_univ_five]
  simp only [Pi.one_apply, one_smul, Pi.smul_apply, smul_eq_mul, one_mul]
  ring

theorem Q_Tinv (x : Fin 5 → ZMod 5) :
    fiveForm 4 true
      (((fiveT⁻¹ : GL (Fin 5) (ZMod 5)) : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ x)
      (((fiveT⁻¹ : GL (Fin 5) (ZMod 5)) : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ x) =
      FiveSquareFrameGeneration.Q x := by
  rw [← Q_T (((fiveT⁻¹ : GL (Fin 5) (ZMod 5)) :
    Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ x)]
  rw [Matrix.mulVec_mulVec]
  simp [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_inv]

end FiveHom

private theorem det_sq_eq_one_of_mem {g : GL (Fin 5) (ZMod 5)}
    (hg : g ∈ fiveReflectionGroup 4 true true) :
    ((Matrix.GeneralLinearGroup.det g : (ZMod 5)ˣ) : ZMod 5) ^ 2 = 1 := by
  classical
  refine Subgroup.closure_induction (p := fun g _ =>
    ((Matrix.GeneralLinearGroup.det g : (ZMod 5)ˣ) : ZMod 5) ^ 2 = 1) ?_ ?_ ?_ ?_ hg
  · intro r hr
    obtain ⟨x, hx, hπ, rfl⟩ := exists_eq_fiveReflOf hr
    have hrr : fiveReflOf 4 true x * fiveReflOf 4 true x = 1 := by
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_one]
      exact fiveReflMatrix_mul_self 4 true x
    have hdet : Matrix.GeneralLinearGroup.det (fiveReflOf 4 true x) *
        Matrix.GeneralLinearGroup.det (fiveReflOf 4 true x) = 1 := by
      rw [← map_mul, hrr, map_one]
    rw [pow_two, ← Units.val_mul, hdet]
    rfl
  · simp
  · intro x y hx hy hpx hpy
    rw [map_mul, Units.val_mul, mul_pow, hpx, hpy, one_mul]
  · intro x hx hpx
    rw [map_inv, Units.val_inv_eq_inv_val, inv_pow, hpx, inv_one]

namespace FiveHom

theorem fivePlusMap_apply_vec (g : GL (Fin 5) (ZMod 5)) (x : Fin 5 → ZMod 5) :
    fiveGLEquiv (fivePlusMap g) x =
      ((Matrix.GeneralLinearGroup.det g : (ZMod 5)ˣ) : ZMod 5) •
        ((fiveT * g * fiveT⁻¹ : GL (Fin 5) (ZMod 5)) :
          Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ x := by
  rw [fiveGLEquiv_apply,
    show fivePlusMap g = Matrix.GeneralLinearGroup.scalar (Fin 5)
      (Matrix.GeneralLinearGroup.det g) * (fiveT * g * fiveT⁻¹) from rfl]
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply]
  ext i
  rw [← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]
  rfl

end FiveHom

open FiveHom

theorem fivePlusMap_mem_O {g : GL (Fin 5) (ZMod 5)} (hg : g ∈ fiveReflectionGroup 4 true true) :
    fiveGLEquiv (fivePlusMap g) ∈ FiveSquareFrameGeneration.O := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro x
  rw [fivePlusMap_apply_vec, Q_smul, det_sq_eq_one_of_mem hg, one_mul]
  have hmat : (((fiveT * g * fiveT⁻¹ : GL (Fin 5) (ZMod 5)) :
      Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ x) =
      (fiveT : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ
        ((g : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ
          (((fiveT⁻¹ : GL (Fin 5) (ZMod 5)) :
            Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ x)) := by
    simp only [Matrix.GeneralLinearGroup.coe_mul]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [hmat, Q_T, fiveForm_mulVec_of_mem hg, Q_Tinv]

private def zx : Fin 5 → ZMod 5 := Pi.single 4 1

private theorem fiveForm_zx : fiveForm 4 true zx zx = 4 := by
  simp [zx, fiveForm, Fin.sum_univ_four, Pi.single_apply]
  decide

private theorem isSquare_four : IsSquare (4 : ZMod 5) := ⟨2, by decide⟩

private theorem fiveT_matrix :
    ((fiveT : GL (Fin 5) (ZMod 5)) : Matrix (Fin 5) (Fin 5) (ZMod 5)) =
      Matrix.diagonal ![1, 1, 1, 1, 2] := rfl

private theorem fiveT_inv_matrix :
    ((fiveT⁻¹ : GL (Fin 5) (ZMod 5)) : Matrix (Fin 5) (Fin 5) (ZMod 5)) =
      Matrix.diagonal ![1, 1, 1, 1, 3] := by
  rw [Matrix.GeneralLinearGroup.coe_inv, fiveT_matrix]
  have h : (Matrix.diagonal ![1, 1, 1, 1, 3] :
      Matrix (Fin 5) (Fin 5) (ZMod 5)) * Matrix.diagonal ![1, 1, 1, 1, 2] = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal] <;> decide
  rw [Matrix.inv_eq_left_inv h]

private theorem fiveReflOf_zx_matrix :
    ((fiveReflOf 4 true zx : GL (Fin 5) (ZMod 5)) :
      Matrix (Fin 5) (Fin 5) (ZMod 5)) =
      Matrix.diagonal ![1, 1, 1, 1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fiveReflOf, fiveReflMatrix, zx, fiveFormVec, fiveForm, Fin.sum_univ_four,
      Pi.single_apply, Matrix.vecMulVec_apply] <;> decide

private theorem det_zx_coe :
    ((Matrix.GeneralLinearGroup.det (fiveReflOf 4 true zx) : (ZMod 5)ˣ) : ZMod 5) = -1 := by
  change Matrix.det ((fiveReflOf 4 true zx : GL (Fin 5) (ZMod 5)) :
    Matrix (Fin 5) (Fin 5) (ZMod 5)) = -1
  rw [fiveReflOf_zx_matrix, Matrix.det_diagonal]
  simp
  decide

private theorem fiveTrT :
    (fiveT : Matrix (Fin 5) (Fin 5) (ZMod 5)) *
        ((fiveReflOf 4 true zx : GL (Fin 5) (ZMod 5)) :
          Matrix (Fin 5) (Fin 5) (ZMod 5)) *
        ((fiveT⁻¹ : GL (Fin 5) (ZMod 5)) : Matrix (Fin 5) (Fin 5) (ZMod 5)) =
      ((fiveReflOf 4 true zx : GL (Fin 5) (ZMod 5)) :
        Matrix (Fin 5) (Fin 5) (ZMod 5)) := by
  rw [fiveT_matrix, fiveT_inv_matrix, fiveReflOf_zx_matrix,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal] <;> decide

private theorem fivePlusMap_zx_apply (i : Fin 5) :
    fiveGLEquiv (fivePlusMap (fiveReflOf 4 true zx))
        (FiveSquareFrameGeneration.e i) =
      FiveSquareFrameGeneration.z (FiveSquareFrameGeneration.e i) := by
  rw [fivePlusMap_apply_vec, det_zx_coe,
    show ((fiveT * fiveReflOf 4 true zx * fiveT⁻¹ : GL (Fin 5) (ZMod 5)) :
      Matrix (Fin 5) (Fin 5) (ZMod 5)) =
      ((fiveReflOf 4 true zx : GL (Fin 5) (ZMod 5)) :
        Matrix (Fin 5) (Fin 5) (ZMod 5)) from by
        rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul]
        exact fiveTrT]
  rw [fiveReflOf_zx_matrix, FiveSquareFrameGeneration.z_e i]
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [Matrix.mulVec_diagonal, Pi.single_apply, Pi.smul_apply, neg_one_smul,
      FiveSquareFrameGeneration.Generic.e_apply FiveSquareFrameGeneration.F] <;> decide

theorem exists_fivePlusMap_eq_z :
    ∃ r ∈ fiveReflections 4 true true,
      fiveGLEquiv (fivePlusMap r) = FiveSquareFrameGeneration.z := by
  refine ⟨fiveReflOf 4 true zx, ?_, ?_⟩
  · refine fiveReflOf_mem (by rw [fiveForm_zx]; decide) ?_
    rw [fiveForm_zx]
    exact ⟨fun _ => rfl, fun _ => isSquare_four⟩
  · refine Module.Basis.ext' FiveSquareFrameGeneration.e ?_
    intro i
    exact fivePlusMap_zx_apply i

private theorem conj_mem_derived_of_mem_O
    {h x : (Fin 5 → ZMod 5) ≃ₗ[ZMod 5] (Fin 5 → ZMod 5)}
    (hh : h ∈ FiveSquareFrameGeneration.O) (hx : x ∈ FiveSquareFrameGeneration.derived) :
    h * x * h⁻¹ ∈ FiveSquareFrameGeneration.derived := by
  have hle : FiveSquareFrameGeneration.O ≤
      Subgroup.normalizer FiveSquareFrameGeneration.derived := by
    simpa [FiveSquareFrameGeneration.derived] using
      Subgroup.normalizer_commutator_ge_left FiveSquareFrameGeneration.O
        FiveSquareFrameGeneration.O
  exact (Subgroup.mem_normalizer_iff.mp (hle hh) x).mp hx

theorem fivePlusMap_mem_derived {g : GL (Fin 5) (ZMod 5)}
    (hg : g ∈ fiveReflectionGroup 4 true true) :
    fiveGLEquiv (fivePlusMap g) ∈ FiveSquareFrameGeneration.derived := by
  classical
  obtain ⟨r0, hr0, hz⟩ := exists_fivePlusMap_eq_z
  refine Subgroup.closure_induction (p := fun g _ =>
    fiveGLEquiv (fivePlusMap g) ∈ FiveSquareFrameGeneration.derived) ?_ ?_ ?_ ?_ hg
  · intro r hr
    obtain ⟨u, hu, hur⟩ := exists_conj_eq_of_mem_fiveReflections hr0 hr
    have hmem : fiveGLEquiv (fivePlusMap r) =
        fiveGLEquiv (fivePlusMap u) * FiveSquareFrameGeneration.z *
          (fiveGLEquiv (fivePlusMap u))⁻¹ := by
      rw [← hur]
      simp only [map_mul, map_inv, hz]
    rw [hmem]
    exact conj_mem_derived_of_mem_O (fivePlusMap_mem_O hu)
      FiveSquareFrameGeneration.z_mem_derived
  · simpa using (FiveSquareFrameGeneration.derived).one_mem
  · intro x y hx hy hpx hpy
    simpa only [map_mul] using (FiveSquareFrameGeneration.derived).mul_mem hpx hpy
  · intro x hx hpx
    simpa only [map_inv] using (FiveSquareFrameGeneration.derived).inv_mem hpx

private theorem fiveForm_polar (x y : Fin 5 → ZMod 5) :
    (2 : ZMod 5) * fiveForm 4 true x y =
      fiveForm 4 true (x + y) (x + y) - fiveForm 4 true x x - fiveForm 4 true y y := by
  simp [fiveForm, Fin.sum_univ_four, Pi.add_apply, Finset.sum_add_distrib]
  ring

theorem exists_isometry_fivePlusMap_conj
    {h : (Fin 5 → ZMod 5) ≃ₗ[ZMod 5] (Fin 5 → ZMod 5)} (hh : h ∈ FiveSquareFrameGeneration.O) :
    ∃ g : GL (Fin 5) (ZMod 5),
      (∀ x y, fiveForm 4 true ((g : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ x)
        ((g : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ y) = fiveForm 4 true x y) ∧
      ∀ k, fiveGLEquiv (fivePlusMap (g * k * g⁻¹)) = h * fiveGLEquiv (fivePlusMap k) * h⁻¹ := by
  classical
  let H : GL (Fin 5) (ZMod 5) := fiveGLEquiv.symm h
  have hH : fiveGLEquiv H = h := MulEquiv.apply_symm_apply fiveGLEquiv h
  let g : GL (Fin 5) (ZMod 5) := fiveT⁻¹ * H * fiveT
  refine ⟨g, ?_, ?_⟩
  · have hgmat : ((g : GL (Fin 5) (ZMod 5)) : Matrix (Fin 5) (Fin 5) (ZMod 5)) =
        ((fiveT⁻¹ : GL (Fin 5) (ZMod 5)) : Matrix (Fin 5) (Fin 5) (ZMod 5)) *
          (H : Matrix (Fin 5) (Fin 5) (ZMod 5)) *
          ((fiveT : GL (Fin 5) (ZMod 5)) : Matrix (Fin 5) (Fin 5) (ZMod 5)) := by
      simp only [g, Matrix.GeneralLinearGroup.coe_mul]
    have hQp : ∀ z, fiveForm 4 true
        (((g : GL (Fin 5) (ZMod 5)) : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ z)
        (((g : GL (Fin 5) (ZMod 5)) : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ z) =
        fiveForm 4 true z z := by
      intro z
      have hvec : ((g : GL (Fin 5) (ZMod 5)) :
          Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ z =
          ((fiveT⁻¹ : GL (Fin 5) (ZMod 5)) : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ
            ((H : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ
              (((fiveT : GL (Fin 5) (ZMod 5)) :
                Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ z)) := by
        rw [hgmat, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      rw [hvec, Q_Tinv]
      have hHapply : (H : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ
          (((fiveT : GL (Fin 5) (ZMod 5)) :
            Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ z) =
          h (((fiveT : GL (Fin 5) (ZMod 5)) :
            Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ z) := by
        rw [← fiveGLEquiv_apply H, hH]
      rw [hHapply, TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hh, Q_T]
    intro x y
    have h2 : (2 : ZMod 5) ≠ 0 := by decide
    apply mul_left_cancel₀ h2
    rw [fiveForm_polar, fiveForm_polar]
    have hadd : ((g : GL (Fin 5) (ZMod 5)) : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ x +
        ((g : GL (Fin 5) (ZMod 5)) : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ y =
        ((g : GL (Fin 5) (ZMod 5)) : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ (x + y) := by
      rw [Matrix.mulVec_add]
    rw [hadd, hQp, hQp, hQp]
  · intro k
    have hpsi : fivePlusMap g =
        Matrix.GeneralLinearGroup.scalar (Fin 5) (Matrix.GeneralLinearGroup.det H) * H := by
      have hg : (fiveT * g * fiveT⁻¹ : GL (Fin 5) (ZMod 5)) = H := by
        simp only [g]
        group
      have hdet : Matrix.GeneralLinearGroup.det g = Matrix.GeneralLinearGroup.det H := by
        simp only [g, map_mul, map_inv]
        rw [mul_assoc,
          mul_comm (Matrix.GeneralLinearGroup.det H)
            (Matrix.GeneralLinearGroup.det fiveT),
          ← mul_assoc, inv_mul_cancel, one_mul]
      rw [show fivePlusMap g = Matrix.GeneralLinearGroup.scalar (Fin 5)
        (Matrix.GeneralLinearGroup.det g) * (fiveT * g * fiveT⁻¹) from rfl, hdet, hg]
    have hc : ∀ z : (Fin 5 → ZMod 5) ≃ₗ[ZMod 5] (Fin 5 → ZMod 5),
        fiveGLEquiv (Matrix.GeneralLinearGroup.scalar (Fin 5)
          (Matrix.GeneralLinearGroup.det H)) * z =
          z * fiveGLEquiv (Matrix.GeneralLinearGroup.scalar (Fin 5)
            (Matrix.GeneralLinearGroup.det H)) := by
      intro z
      obtain ⟨Z, rfl⟩ : ∃ Z, fiveGLEquiv Z = z :=
        ⟨fiveGLEquiv.symm z, MulEquiv.apply_symm_apply fiveGLEquiv z⟩
      rw [← map_mul, ← map_mul, Matrix.GeneralLinearGroup.scalar_commute]
    have hpsi_apply : fiveGLEquiv (fivePlusMap g) =
        fiveGLEquiv (Matrix.GeneralLinearGroup.scalar (Fin 5)
          (Matrix.GeneralLinearGroup.det H)) * h := by
      rw [hpsi, map_mul, hH]
    simp only [map_mul, map_inv]
    rw [hpsi_apply, _root_.mul_inv_rev]
    calc (fiveGLEquiv (Matrix.GeneralLinearGroup.scalar (Fin 5)
          (Matrix.GeneralLinearGroup.det H)) * h) *
          fiveGLEquiv (fivePlusMap k) *
          (h⁻¹ * (fiveGLEquiv (Matrix.GeneralLinearGroup.scalar (Fin 5)
            (Matrix.GeneralLinearGroup.det H)))⁻¹) =
        fiveGLEquiv (Matrix.GeneralLinearGroup.scalar (Fin 5)
          (Matrix.GeneralLinearGroup.det H)) *
          (h * fiveGLEquiv (fivePlusMap k) * h⁻¹) *
          (fiveGLEquiv (Matrix.GeneralLinearGroup.scalar (Fin 5)
            (Matrix.GeneralLinearGroup.det H)))⁻¹ := by group
      _ = (h * fiveGLEquiv (fivePlusMap k) * h⁻¹) *
          fiveGLEquiv (Matrix.GeneralLinearGroup.scalar (Fin 5)
            (Matrix.GeneralLinearGroup.det H)) *
          (fiveGLEquiv (Matrix.GeneralLinearGroup.scalar (Fin 5)
            (Matrix.GeneralLinearGroup.det H)))⁻¹ := by
        rw [hc (h * fiveGLEquiv (fivePlusMap k) * h⁻¹)]
      _ = h * fiveGLEquiv (fivePlusMap k) * h⁻¹ := by group

theorem commute_of_fivePlusMap_eq_one {g : GL (Fin 5) (ZMod 5)} (hg : fivePlusMap g = 1)
    (h : GL (Fin 5) (ZMod 5)) : Commute g h := by
  let u : (ZMod 5)ˣ := Matrix.GeneralLinearGroup.det g
  let c : GL (Fin 5) (ZMod 5) := Matrix.GeneralLinearGroup.scalar (Fin 5) u
  have hg' : c * (fiveT * g * fiveT⁻¹) = 1 := hg
  have hmain : fiveT * g * fiveT⁻¹ = c⁻¹ := by
    calc fiveT * g * fiveT⁻¹ = 1 * (fiveT * g * fiveT⁻¹) := by rw [one_mul]
      _ = (c⁻¹ * c) * (fiveT * g * fiveT⁻¹) := by rw [inv_mul_cancel]
      _ = c⁻¹ * (c * (fiveT * g * fiveT⁻¹)) := by rw [mul_assoc]
      _ = c⁻¹ * 1 := by rw [hg']
      _ = c⁻¹ := by rw [mul_one]
  have hcomm : c⁻¹ * fiveT = fiveT * c⁻¹ := by
    change ((Matrix.GeneralLinearGroup.scalar (Fin 5) u))⁻¹ * fiveT = _
    rw [← map_inv]
    exact Matrix.GeneralLinearGroup.scalar_commute u⁻¹ fiveT
  have hg_eq : g = c⁻¹ := by
    calc g = fiveT⁻¹ * (fiveT * g * fiveT⁻¹) * fiveT := by group
      _ = fiveT⁻¹ * c⁻¹ * fiveT := by rw [hmain]
      _ = c⁻¹ := by
        rw [mul_assoc, hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [hg_eq]
  change c⁻¹ * h = h * c⁻¹
  rw [show c⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 5) (u⁻¹) from by
    change ((Matrix.GeneralLinearGroup.scalar (Fin 5) u))⁻¹ = _
    rw [← map_inv]]
  exact Matrix.GeneralLinearGroup.scalar_commute u⁻¹ h

end CFSG.OddTranspositions.PartThree
