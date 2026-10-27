module

public import CFSG.GH74.KGroups.L3EpsBlockLin
public import CFSG.GH74.KGroups.L3EpsCenter
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCoprimeCentral
public import CFSG.GH74.KGroups.L3EpsNoNormalThree
public import CFSG.GH74.KGroups.L3EpsOutExp
public import CFSG.GH74.KGroups.L3EpsOuterLin
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearDescentFixedBasis
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherScalarSquareSplit
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
import CFSG.Walter.Defs
import Certificates.Certificate1
import Certificates.Certificate2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.L3Lin

open Matrix Subgroup CFSG.GH74.KGroups.L3Eps CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] def blk (A : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 2) (Fin 2) F :=
  !![A 0 0, A 0 1; A 1 0, A 1 1]

theorem blk_mul {A B : Matrix (Fin 3) (Fin 3) F} (h02 : A 0 2 = 0) (h12 : A 1 2 = 0) :
    blk (A * B) = blk A * blk B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, h02, h12]

theorem blk_one : blk (1 : Matrix (Fin 3) (Fin 3) F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk]

@[expose] noncomputable def dG : GL (Fin 3) F := SpecialLinearGroup.toGL dNeg

theorem coe_dG : ((dG : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = (dNeg : SL(3, F)).1 :=
  rfl

variable (F) in
abbrev CenG : Subgroup (GL (Fin 3) F) := centralizer {dG}

theorem mul_dG_of_mem {A : GL (Fin 3) F} (hA : A ∈ CenG F) :
    (A : Matrix (Fin 3) (Fin 3) F) * (dNeg : SL(3, F)).1 =
      (dNeg : SL(3, F)).1 * (A : Matrix (Fin 3) (Fin 3) F) := by
  have h := congrArg (fun B : GL (Fin 3) F => (B : Matrix (Fin 3) (Fin 3) F))
    (mem_centralizer_singleton_iff.1 hA)
  simpa only [Units.val_mul, coe_dG] using h

theorem entries_of_mem_CenG (h2 : (2 : F) ≠ 0) {A : GL (Fin 3) F} (hA : A ∈ CenG F) :
    (A : Matrix (Fin 3) (Fin 3) F) 0 2 = 0 ∧ (A : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 ∧
      (A : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧ (A : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 :=
  entries_of_commute_dNeg h2 (mul_dG_of_mem hA)

theorem mem_CenG_of_entries {A : GL (Fin 3) F} (h02 : (A : Matrix (Fin 3) (Fin 3) F) 0 2 = 0)
    (h12 : (A : Matrix (Fin 3) (Fin 3) F) 1 2 = 0) (h20 : (A : Matrix (Fin 3) (Fin 3) F) 2 0 = 0)
    (h21 : (A : Matrix (Fin 3) (Fin 3) F) 2 1 = 0) : A ∈ CenG F := by
  rw [mem_centralizer_singleton_iff]
  apply Units.ext
  simp only [Units.val_mul, coe_dG]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_dNeg, Matrix.mul_apply, Fin.sum_univ_three, h02, h12, h20, h21]

theorem corner_mul (h2 : (2 : F) ≠ 0) {A B : GL (Fin 3) F} (hA : A ∈ CenG F) :
    ((A * B : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 2 =
      (A : Matrix (Fin 3) (Fin 3) F) 2 2 * (B : Matrix (Fin 3) (Fin 3) F) 2 2 := by
  obtain ⟨-, -, h20, h21⟩ := entries_of_mem_CenG h2 hA
  simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, h20, h21]

theorem det_eq_of_mem_CenG (h2 : (2 : F) ≠ 0) {A : GL (Fin 3) F} (hA : A ∈ CenG F) :
    (A : Matrix (Fin 3) (Fin 3) F).det =
      (blk (A : Matrix (Fin 3) (Fin 3) F)).det * (A : Matrix (Fin 3) (Fin 3) F) 2 2 := by
  obtain ⟨h02, h12, h20, h21⟩ := entries_of_mem_CenG h2 hA
  rw [Matrix.det_fin_three, Matrix.det_fin_two, h02, h12, h20, h21]
  simp only [blk, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

theorem corner_ne_zero (h2 : (2 : F) ≠ 0) {A : GL (Fin 3) F} (hA : A ∈ CenG F) :
    (A : Matrix (Fin 3) (Fin 3) F) 2 2 ≠ 0 := by
  intro h
  have hd := det_eq_of_mem_CenG h2 hA
  rw [h, mul_zero] at hd
  exact A.isUnit.map Matrix.detMonoidHom |>.ne_zero hd

@[expose] noncomputable def blkHom (h2 : (2 : F) ≠ 0) : ↥(CenG F) →* GL (Fin 2) F where
  toFun A :=
    { val := blk ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
      inv := blk (((A : GL (Fin 3) F)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
      val_inv := by
        obtain ⟨h02, h12, -, -⟩ := entries_of_mem_CenG h2 A.2
        rw [← blk_mul h02 h12, ← Units.val_mul, mul_inv_cancel, Units.val_one, blk_one]
      inv_val := by
        obtain ⟨h02, h12, -, -⟩ := entries_of_mem_CenG h2 (inv_mem A.2)
        rw [← blk_mul h02 h12, ← Units.val_mul, inv_mul_cancel, Units.val_one, blk_one] }
  map_one' := Units.ext blk_one
  map_mul' A B := by
    obtain ⟨h02, h12, -, -⟩ := entries_of_mem_CenG h2 A.2
    exact Units.ext (by simp only [Subgroup.coe_mul, Units.val_mul]; exact blk_mul h02 h12)

theorem coe_blkHom (h2 : (2 : F) ≠ 0) (A : ↥(CenG F)) :
    ((blkHom h2 A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      blk ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) :=
  rfl

theorem commute_of_conjAut [Finite F] {A T : GL (Fin 3) F}
    (hT : (T : Matrix (Fin 3) (Fin 3) F).trace ≠ 0)
    (h : conjAut 3 F A * conjAut 3 F T = conjAut 3 F T * conjAut 3 F A) : A * T = T * A := by
  have h1 : conjAut 3 F (A * T * A⁻¹ * T⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h]
    group
  obtain ⟨u, hu⟩ := (ProjectivePlane.conjAut_eq_one_iff (by norm_num) _).1 h1
  have h3 : A * T * A⁻¹ = GeneralLinearGroup.scalar (Fin 3) u * T := by
    rw [← hu]
    group
  have htr := congrArg (fun B : GL (Fin 3) F => (B : Matrix (Fin 3) (Fin 3) F).trace) h3
  simp only [Units.val_mul, Matrix.trace_mul_cycle (A : Matrix (Fin 3) (Fin 3) F),
    Units.inv_mul, one_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.trace_mul_comm (Matrix.diagonal fun _ => (u : F))] at htr
  have hd : ((T : Matrix (Fin 3) (Fin 3) F) * Matrix.diagonal fun _ => (u : F)).trace =
      (u : F) * (T : Matrix (Fin 3) (Fin 3) F).trace := by
    simp [Matrix.trace, Matrix.mul_diagonal, Finset.mul_sum, mul_comm]
  have htr' : (T : Matrix (Fin 3) (Fin 3) F).trace =
      (u : F) * (T : Matrix (Fin 3) (Fin 3) F).trace := htr.trans hd
  have hu1 : (u : F) = 1 := by
    have : (T : Matrix (Fin 3) (Fin 3) F).trace * (1 - (u : F)) = 0 := by
      linear_combination htr'
    exact (sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hT)).symm
  have hu1' : u = 1 := Units.ext hu1
  rw [hu1', map_one, one_mul] at h3
  calc A * T = A * T * A⁻¹ * A := by group
    _ = T * A := by rw [h3]

@[expose] noncomputable def cornerHom (h2 : (2 : F) ≠ 0) : ↥(CenG F) →* Fˣ where
  toFun A := Units.mk0 (((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 2)
    (corner_ne_zero h2 A.2)
  map_one' := by ext; simp
  map_mul' A B := by
    ext
    simp only [Subgroup.coe_mul, Units.val_mk0, Units.val_mul]
    exact corner_mul h2 A.2

theorem coe_cornerHom (h2 : (2 : F) ≠ 0) (A : ↥(CenG F)) :
    ((cornerHom h2 A : Fˣ) : F) = ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 2 :=
  rfl

theorem scalar_mem_CenG (u : Fˣ) : GeneralLinearGroup.scalar (Fin 3) u ∈ CenG F := by
  rw [mem_centralizer_singleton_iff]
  exact ((Subgroup.mem_center_iff.1 (by
    rw [GeneralLinearGroup.center_eq_range_scalar]; exact ⟨u, rfl⟩)) dG).symm

theorem eq_one_of_scalar_corner (h2 : (2 : F) ≠ 0) {A : ↥(CenG F)} {u : Fˣ}
    (hA : (A : GL (Fin 3) F) = GeneralLinearGroup.scalar (Fin 3) u) (h1 : cornerHom h2 A = 1) :
    u = 1 := by
  have h := congrArg Units.val h1
  rw [coe_cornerHom, hA] at h
  simpa using h

variable (F) in
@[expose] noncomputable def eA : MulAut (projectiveSL 3 F) := MulAut.conj (proj 3 F eSL)

variable (F) in
@[expose] noncomputable def rA : MulAut (projectiveSL 3 F) := MulAut.conj (proj 3 F rSL)

theorem conjAut_toGL_eq (s : SL(3, F)) :
    conjAut 3 F (SpecialLinearGroup.toGL s) = MulAut.conj (proj 3 F s) := by
  ext x
  obtain ⟨g, rfl⟩ := proj_surjective 3 F x
  rw [conjAut_proj, MulAut.conj_apply, ← map_mul, ← map_inv, ← map_mul]
  congr 1
  apply SpecialLinearGroup.toGL_injective
  rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation]
  simp only [map_mul, map_inv]

theorem eSL_sq : (eSL : SL(3, F)) ^ 2 = dNeg := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sq, coe_eSL, eMat, coe_dNeg, Matrix.mul_apply, Fin.sum_univ_three]

theorem eA_sq : eA F ^ 2 = conjAut 3 F dG := by
  rw [eA, ← conjAut_toGL_eq, ← map_pow, ← map_pow, eSL_sq]
  rfl

variable (F) in
noncomputable abbrev CS : Subgroup (MulAut (projectiveSL 3 F)) :=
  (conjAut 3 F).range ⊓ centralizer ({eA F ^ 2} : Set (MulAut (projectiveSL 3 F)))

theorem conjAut_mem_CS {A : GL (Fin 3) F} (hA : A ∈ CenG F) : conjAut 3 F A ∈ CS F := by
  refine Subgroup.mem_inf.2 ⟨⟨A, rfl⟩, ?_⟩
  rw [mem_centralizer_singleton_iff, eA_sq, ← map_mul, ← map_mul,
    (mem_centralizer_singleton_iff.1 hA)]

@[expose] noncomputable def piC : ↥(CenG F) →* ↥(CS F) :=
  ((conjAut 3 F).comp (CenG F).subtype).codRestrict _ fun A => conjAut_mem_CS A.2

theorem coe_piC (A : ↥(CenG F)) : (piC A : MulAut (projectiveSL 3 F)) = conjAut 3 F A :=
  rfl

theorem trace_dG : ((dG : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).trace = -1 := by
  rw [coe_dG, coe_dNeg]
  simp [Matrix.trace, Fin.sum_univ_three]

theorem piC_surjective [Finite F] : Function.Surjective (piC (F := F)) := by
  rintro ⟨x, hx⟩
  obtain ⟨⟨A, rfl⟩, hx⟩ := Subgroup.mem_inf.1 hx
  rw [mem_centralizer_singleton_iff, eA_sq] at hx
  have hA : A * dG = dG * A :=
    commute_of_conjAut (by rw [trace_dG]; exact neg_ne_zero.2 one_ne_zero) hx
  exact ⟨⟨A, mem_centralizer_singleton_iff.2 hA⟩, rfl⟩

theorem commute_of_piC [Finite F] (h2 : (2 : F) ≠ 0) {A B : ↥(CenG F)}
    (h : piC A * piC B = piC B * piC A) : A * B = B * A := by
  have h1 : conjAut 3 F ((A * B * A⁻¹ * B⁻¹ : ↥(CenG F)) : GL (Fin 3) F) = 1 := by
    have h' := congrArg Subtype.val h
    simp only [Subgroup.coe_mul, coe_piC] at h'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, h']
    group
  obtain ⟨u, hu⟩ := (ProjectivePlane.conjAut_eq_one_iff (by norm_num) _).1 h1
  have hu1 : u = 1 := eq_one_of_scalar_corner h2 hu (by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_right_comm (cornerHom h2 A),
      mul_inv_cancel, one_mul, mul_inv_cancel])
  rw [hu1, map_one] at hu
  have h3 : A * B * A⁻¹ * B⁻¹ = 1 := Subtype.ext hu
  calc A * B = A * B * A⁻¹ * B⁻¹ * (B * A) := by group
    _ = B * A := by rw [h3, one_mul]

theorem ker_piC_le [Finite F] (h2 : (2 : F) ≠ 0) :
    (piC (F := F)).ker ≤ ((Matrix.ProjGenLinGroup.mk).comp (blkHom h2)).ker := by
  intro A hA
  rw [MonoidHom.mem_ker] at hA ⊢
  have h1 : conjAut 3 F (A : GL (Fin 3) F) = 1 := congrArg Subtype.val hA
  obtain ⟨u, hu⟩ := (ProjectivePlane.conjAut_eq_one_iff (by norm_num) _).1 h1
  rw [MonoidHom.comp_apply, Matrix.ProjGenLinGroup.mk_eq_one,
    GeneralLinearGroup.center_eq_range_scalar]
  refine ⟨u, Units.ext ?_⟩
  rw [coe_blkHom, hu]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk]

@[expose] noncomputable def rho [Finite F] (h2 : (2 : F) ≠ 0) : ↥(CS F) →* PGL(Fin 2, F) :=
  (piC (F := F)).liftOfSurjective piC_surjective
    ⟨(Matrix.ProjGenLinGroup.mk).comp (blkHom h2), ker_piC_le h2⟩

theorem rho_piC [Finite F] (h2 : (2 : F) ≠ 0) (A : ↥(CenG F)) :
    rho h2 (piC A) = Matrix.ProjGenLinGroup.mk (blkHom h2 A) :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ A

end CFSG.LocalAnalysis.UniquenessCase.UC22.L3Lin
