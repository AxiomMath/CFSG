module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aL3E

public section

namespace CFSG.Quasithin.H13.Ch4.B414.M

open CFSG.Open hiding StatedSL StatedSp
open CFSG.Quasithin CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Matrix

variable {F : Type} [Field F]

@[expose] def w0 : Matrix (Fin 3) (Fin 3) F := !![0, 0, 1; 0, 1, 0; 1, 0, 0]

theorem w0_mul_w0 : (w0 : Matrix (Fin 3) (Fin 3) F) * w0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [w0, Matrix.mul_apply, Fin.sum_univ_three]

theorem w0_transpose : (w0 : Matrix (Fin 3) (Fin 3) F)ᵀ = w0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem det_w0_mul_self : (w0 : Matrix (Fin 3) (Fin 3) F).det * w0.det = 1 := by
  rw [← Matrix.det_mul, w0_mul_w0, Matrix.det_one]

@[expose] def thetaMat (A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F :=
  w0 * ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ * w0

theorem w0_conj_mul (X Y : Matrix (Fin 3) (Fin 3) F) :
    w0 * X * w0 * (w0 * Y * w0) = w0 * (X * Y) * w0 := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc w0 w0, w0_mul_w0, Matrix.one_mul]

theorem w0_conj_one : (w0 : Matrix (Fin 3) (Fin 3) F) * 1 * w0 = 1 := by
  rw [Matrix.mul_one, w0_mul_w0]

@[expose] def thetaGL (A : GL (Fin 3) F) : GL (Fin 3) F where
  val := thetaMat A
  inv := w0 * (A : Matrix (Fin 3) (Fin 3) F)ᵀ * w0
  val_inv := by
    rw [thetaMat, w0_conj_mul, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one,
      w0_conj_one]
  inv_val := by
    rw [thetaMat, w0_conj_mul, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one,
      w0_conj_one]

theorem coe_thetaGL (A : GL (Fin 3) F) :
    ((thetaGL A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = thetaMat A := rfl

theorem coe_thetaGL_inv (A : GL (Fin 3) F) :
    (((thetaGL A)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      w0 * (A : Matrix (Fin 3) (Fin 3) F)ᵀ * w0 := rfl

theorem thetaGL_mul (A B : GL (Fin 3) F) : thetaGL (A * B) = thetaGL A * thetaGL B := by
  apply Units.ext
  rw [Units.val_mul, coe_thetaGL, coe_thetaGL, coe_thetaGL, thetaMat, thetaMat, thetaMat,
    w0_conj_mul, _root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

theorem thetaGL_thetaGL (A : GL (Fin 3) F) : thetaGL (thetaGL A) = A := by
  apply Units.ext
  rw [coe_thetaGL, thetaMat, coe_thetaGL_inv, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, w0_transpose]
  have h : (w0 : Matrix (Fin 3) (Fin 3) F) * (w0 * ((A : Matrix (Fin 3) (Fin 3) F) * w0)) * w0 =
      (w0 * w0) * (A : Matrix (Fin 3) (Fin 3) F) * (w0 * w0) := by
    simp only [Matrix.mul_assoc]
  rw [h, w0_mul_w0, Matrix.one_mul, Matrix.mul_one]

@[expose] def thetaEquiv (F : Type) [Field F] : GL (Fin 3) F ≃* GL (Fin 3) F where
  toFun := thetaGL
  invFun := thetaGL
  left_inv := thetaGL_thetaGL
  right_inv := thetaGL_thetaGL
  map_mul' := thetaGL_mul

@[expose] noncomputable def graphAut (F : Type) [Field F] : PGL3 F ≃* PGL3 F :=
  QuotientGroup.congr (Subgroup.center (GL (Fin 3) F)) (Subgroup.center (GL (Fin 3) F))
    (thetaEquiv F) (Subgroup.map_center_eq (thetaEquiv F))

theorem graphAut_mk (g : GL (Fin 3) F) :
    graphAut F (ProjGenLinGroup.mk g) = ProjGenLinGroup.mk (thetaGL g) := rfl

theorem graphAut_graphAut (y : PGL3 F) : graphAut F (graphAut F y) = y := by
  obtain ⟨g, rfl⟩ := ProjGenLinGroup.mk_surjective y
  rw [graphAut_mk, graphAut_mk, thetaGL_thetaGL]

theorem mem_stabilizer_one_iff {A : SpecialLinearGroup (Fin 3) F} :
    A ∈ stabilizer (flagSpace 3 F 1) ↔
      (A : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 ∧ (A : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 := by
  constructor
  · intro hA
    have he : (Pi.single 0 1 : Fin 3 → F) ∈ flagSpace 3 F 1 := by
      rw [mem_flagSpace]
      intro j hj
      fin_cases j <;> simp_all
    have h1 : (A : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1 ∈ flagSpace 3 F 1 := by
      rw [← mem_stabilizer.mp hA]
      exact ⟨_, he, rfl⟩
    rw [mem_flagSpace] at h1
    have a1 := h1 1 (by simp)
    have a2 := h1 2 (by simp)
    simp only [Matrix.mulVec_single_one] at a1 a2
    exact ⟨a1, a2⟩
  · rintro ⟨h10, h20⟩
    refine mem_stabilizer_of_map_le ?_
    rintro _ ⟨v, hv, rfl⟩
    have hv' := (mem_flagSpace).mp hv
    rw [mem_flagSpace]
    have hv1 := hv' 1 (by simp)
    have hv2 := hv' 2 (by simp)
    intro j hj
    show ((A : Matrix (Fin 3) (Fin 3) F) *ᵥ v) j = 0
    fin_cases j
    · simp at hj
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hv1, hv2, h10]
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hv1, hv2, h20]

theorem mem_stabilizer_two_iff {A : SpecialLinearGroup (Fin 3) F} :
    A ∈ stabilizer (flagSpace 3 F 2) ↔
      (A : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧ (A : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 := by
  constructor
  · intro hA
    have he : ∀ i : Fin 3, (i : ℕ) < 2 → (Pi.single i 1 : Fin 3 → F) ∈ flagSpace 3 F 2 := by
      intro i hi
      rw [mem_flagSpace]
      intro j hj
      have : i ≠ j := fun h => by subst h; omega
      simp [this.symm]
    have h1 : ∀ i : Fin 3, (i : ℕ) < 2 →
        (A : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single i 1 ∈ flagSpace 3 F 2 := by
      intro i hi
      rw [← mem_stabilizer.mp hA]
      exact ⟨_, he i hi, rfl⟩
    have a0 := h1 0 (by simp)
    have a1 := h1 1 (by simp)
    rw [mem_flagSpace] at a0 a1
    have b0 := a0 2 (by simp)
    have b1 := a1 2 (by simp)
    simp only [Matrix.mulVec_single_one] at b0 b1
    exact ⟨b0, b1⟩
  · rintro ⟨h20, h21⟩
    refine mem_stabilizer_of_map_le ?_
    rintro _ ⟨v, hv, rfl⟩
    have hv' := (mem_flagSpace).mp hv
    rw [mem_flagSpace]
    have hv2 := hv' 2 (by simp)
    intro j hj
    show ((A : Matrix (Fin 3) (Fin 3) F) *ᵥ v) j = 0
    fin_cases j
    · simp at hj
    · simp at hj
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hv2, h20, h21]

@[expose] def thetaSL (A : SpecialLinearGroup (Fin 3) F) : SpecialLinearGroup (Fin 3) F :=
  ⟨w0 * ((A⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ * w0, by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, (A⁻¹).2, mul_one,
      det_w0_mul_self]⟩

theorem toGL_thetaSL (A : SpecialLinearGroup (Fin 3) F) :
    SpecialLinearGroup.toGL (thetaSL A) = thetaGL (SpecialLinearGroup.toGL A) := by
  apply Units.ext
  rw [coe_thetaGL, thetaMat, ← map_inv]
  simp only [SpecialLinearGroup.coe_GL_coe_matrix]
  rfl

theorem thetaSL_entries (A : SpecialLinearGroup (Fin 3) F) (i j : Fin 3) :
    (thetaSL A : Matrix (Fin 3) (Fin 3) F) i j =
      ((A⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) (2 - j) (2 - i) := by
  show (w0 * ((A⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ * w0 :
    Matrix (Fin 3) (Fin 3) F) i j = _
  generalize ((A⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = B
  fin_cases i <;> fin_cases j <;>
    simp [w0, Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul, dotProduct]

theorem graphAut_mem_of_mem {j₁ j₂ : Fin 2} {y : PGL3 F}
    (hθ : ∀ A : SpecialLinearGroup (Fin 3) F, A ∈ stabilizer (flagSpace 3 F ((j₁ : ℕ) + 1)) →
      thetaSL A ∈ stabilizer (flagSpace 3 F ((j₂ : ℕ) + 1)))
    (hy : y ∈ Ptheta F j₁) : graphAut F y ∈ Ptheta F j₂ := by
  obtain ⟨x, ⟨A, hA, rfl⟩, rfl⟩ := hy
  refine ⟨proj 3 F (thetaSL A), ⟨thetaSL A, hθ A hA, rfl⟩, ?_⟩
  rw [thetaP_proj, thetaP_proj, graphAut_mk, toGL_thetaSL]

theorem thetaSL_mem_zero {A : SpecialLinearGroup (Fin 3) F}
    (hA : A ∈ stabilizer (flagSpace 3 F (((1 : Fin 2) : ℕ) + 1))) :
    thetaSL A ∈ stabilizer (flagSpace 3 F (((0 : Fin 2) : ℕ) + 1)) := by
  have hA' : A⁻¹ ∈ stabilizer (flagSpace 3 F 2) := inv_mem hA
  rw [mem_stabilizer_two_iff] at hA'
  show thetaSL A ∈ stabilizer (flagSpace 3 F 1)
  rw [mem_stabilizer_one_iff, thetaSL_entries, thetaSL_entries]
  exact ⟨hA'.2, hA'.1⟩

theorem thetaSL_mem_one {A : SpecialLinearGroup (Fin 3) F}
    (hA : A ∈ stabilizer (flagSpace 3 F (((0 : Fin 2) : ℕ) + 1))) :
    thetaSL A ∈ stabilizer (flagSpace 3 F (((1 : Fin 2) : ℕ) + 1)) := by
  have hA' : A⁻¹ ∈ stabilizer (flagSpace 3 F 1) := inv_mem hA
  rw [mem_stabilizer_one_iff] at hA'
  show thetaSL A ∈ stabilizer (flagSpace 3 F 2)
  rw [mem_stabilizer_two_iff, thetaSL_entries, thetaSL_entries]
  exact ⟨hA'.2, hA'.1⟩

theorem map_graphAut_Ptheta_one : (Ptheta F 1).map (graphAut F).toMonoidHom = Ptheta F 0 := by
  refine le_antisymm ?_ fun y hy => ?_
  · rintro _ ⟨y, hy, rfl⟩
    exact graphAut_mem_of_mem (fun A hA => thetaSL_mem_zero hA) hy
  · exact ⟨graphAut F y, graphAut_mem_of_mem (fun A hA => thetaSL_mem_one hA) hy,
      graphAut_graphAut y⟩

end CFSG.Quasithin.H13.Ch4.B414.M
