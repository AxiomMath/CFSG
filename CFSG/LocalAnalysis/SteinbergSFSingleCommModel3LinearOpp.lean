module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommModel3LinearDefs

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace Model3LinOpp

variable {F' : Type} [Field F']

abbrev uMat (γ β α : F') : Matrix (Fin 3) (Fin 3) F' := !![1, γ, α; 0, 1, β; 0, 0, 1]

theorem uMat_det (γ β α : F') : (uMat γ β α).det = 1 := by
  simp [uMat, Matrix.det_fin_three]

theorem uMat_mem (γ β α : F') :
    (⟨uMat γ β α, uMat_det γ β α⟩ : SpecialLinearGroup (Fin 3) F') ∈ unitriangular 3 F' := by
  refine mem_unitriangular.mpr ⟨fun i j hji => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;>
      first
      | exact absurd hji (by decide)
      | simp [uMat]
  · fin_cases i <;> simp [uMat]

theorem transv_det (s : F') : (transvection (0 : Fin 3) 2 s).det = 1 := by
  simp [transvection, Matrix.det_fin_three, Matrix.single_apply]

theorem transv_mem (s : F') :
    (⟨transvection (0 : Fin 3) 2 s, transv_det s⟩ : SpecialLinearGroup (Fin 3) F') ∈
      unitriangular 3 F' := by
  refine mem_unitriangular.mpr ⟨fun i j hji => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;>
      first
      | exact absurd hji (by decide)
      | simp [transvection, Matrix.single_apply]
  · fin_cases i <;> simp [transvection, Matrix.single_apply]

variable [CharP F' 2]

theorem core_mat (v f : Fin 3 → F') (c s γ β α : F')
    (hf2 : f 2 = f 0 * α) (hγ : γ * f 0 = f 1) (hβ : β * v 2 = v 1)
    (hα : α * v 2 = v 0 + γ * v 1) (hs : s * (v 2 * f 0) = c) :
    transvection (2 : Fin 3) 0 c * uMat γ β α =
      uMat γ β α * (1 + s • Matrix.of fun i j => v i * f j) := by
  have h2 : (2 : F') = 0 := CharTwo.two_eq_zero
  have hfin : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
  have hT : transvection (2 : Fin 3) 0 c = !![1, 0, 0; 0, 1, 0; c, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [transvection, Matrix.single_apply, Matrix.one_apply]
  have hN : (1 : Matrix (Fin 3) (Fin 3) F') + s • Matrix.of (fun i j => v i * f j) =
      !![1 + s * (v 0 * f 0), s * (v 0 * f 1), s * (v 0 * f 2);
        s * (v 1 * f 0), 1 + s * (v 1 * f 1), s * (v 1 * f 2);
        s * (v 2 * f 0), s * (v 2 * f 1), 1 + s * (v 2 * f 2)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]
  rw [hT, hN]
  ext i j
  rcases hfin i with rfl | rfl | rfl <;> rcases hfin j with rfl | rfl | rfl <;>
    simp only [uMat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons] <;>
    (first
      | linear_combination (s * f 0) * hα - (s * f 0 * α * v 2) * h2
      | linear_combination (s * f 1) * hα - (s * f 1 * α * v 2) * h2
      | linear_combination (s * f 2) * hα - (s * f 2 * α * v 2) * h2
      | linear_combination (-(s * f 0)) * hβ - (s * f 0 * v 1) * h2
      | linear_combination (-(s * f 1)) * hβ - (s * f 1 * v 1) * h2
      | linear_combination (-(s * f 2)) * hβ - (s * f 2 * v 1) * h2
      | linear_combination (-1 : F') * hs
      | linear_combination (-γ) * hs + (s * v 2) * hγ
      | linear_combination (-α) * hs - (s * v 2) * hf2)

theorem key_exists (T Ti : Matrix (Fin 3) (Fin 3) F') (hTT : T * Ti = 1) (hTiT : Ti * T = 1)
    (h₁ : linE13 F' * (Ti * linE13 F' * T) ≠ 0) (h₂ : Ti * linE13 F' * T * linE13 F' ≠ 0)
    (c : F') :
    ∃ γ β α s : F', transvection (2 : Fin 3) 0 c * uMat γ β α =
      uMat γ β α * (Ti * transvection (0 : Fin 3) 2 s * T) := by
  have h2 : (2 : F') = 0 := CharTwo.two_eq_zero
  have hvf : T 2 0 * Ti 0 0 + T 2 1 * Ti 1 0 + T 2 2 * Ti 2 0 = 0 := by
    have h := congrFun (congrFun hTT 2) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using h
  have hv2 : Ti 2 0 ≠ 0 := by
    intro h0
    apply h₁
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [linE13, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, h0]
  have hf0 : T 2 0 ≠ 0 := by
    intro h0
    apply h₂
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [linE13, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, h0]
  have hA' : Ti * linE13 F' * T = Matrix.of fun i j => Ti i 0 * T 2 j := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [linE13, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply] <;> ring
  have htr : ∀ s : F', transvection (0 : Fin 3) 2 s = 1 + s • linE13 F' := by
    intro s
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [transvection, linE13, Matrix.single_apply, Matrix.one_apply]
  have hX : ∀ s : F', Ti * transvection (0 : Fin 3) 2 s * T =
      1 + s • Matrix.of fun i j => Ti i 0 * T 2 j := by
    intro s
    rw [htr s, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.add_mul, Matrix.smul_mul,
      hTiT, hA']
  obtain ⟨γ, hγ⟩ : ∃ γ : F', γ * T 2 0 = T 2 1 := ⟨T 2 1 / T 2 0, div_mul_cancel₀ _ hf0⟩
  obtain ⟨β, hβ⟩ : ∃ β : F', β * Ti 2 0 = Ti 1 0 := ⟨Ti 1 0 / Ti 2 0, div_mul_cancel₀ _ hv2⟩
  obtain ⟨α, hα⟩ : ∃ α : F', α * Ti 2 0 = Ti 0 0 + γ * Ti 1 0 :=
    ⟨(Ti 0 0 + γ * Ti 1 0) / Ti 2 0, div_mul_cancel₀ _ hv2⟩
  have hf2 : T 2 2 = T 2 0 * α := by
    have key : (T 2 2 - T 2 0 * α) * Ti 2 0 = 0 := by
      linear_combination hvf - T 2 0 * hα + Ti 1 0 * hγ - T 2 0 * (Ti 0 0 + γ * Ti 1 0) * h2
    exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_right hv2)
  refine ⟨γ, β, α, c / (Ti 2 0 * T 2 0), ?_⟩
  rw [hX]
  exact core_mat (fun i => Ti i 0) (fun j => T 2 j) c _ γ β α hf2 hγ hβ hα
    (div_mul_cancel₀ c (mul_ne_zero hv2 hf0))

end Model3LinOpp

theorem model3_linear_transvection_mem {F' : Type} [Field F'] [CharP F' 2]
    (τ : SpecialLinearGroup (Fin 3) F')
    (h₁ : linE13 F' * linConj τ ≠ 0) (h₂ : linConj τ * linE13 F' ≠ 0)
    (A : SpecialLinearGroup (Fin 3) F') (c : F')
    (hA : (A : Matrix (Fin 3) (Fin 3) F') = transvection 2 0 c) :
    A ∈ unitriangular 3 F' ⊔ (unitriangular 3 F').map (MulAut.conj τ⁻¹).toMonoidHom := by
  have hTT : (τ : Matrix (Fin 3) (Fin 3) F') *
      ((τ⁻¹ : SpecialLinearGroup (Fin 3) F') : Matrix (Fin 3) (Fin 3) F') = 1 := by
    rw [← SpecialLinearGroup.coe_mul, mul_inv_cancel, SpecialLinearGroup.coe_one]
  have hTiT : ((τ⁻¹ : SpecialLinearGroup (Fin 3) F') : Matrix (Fin 3) (Fin 3) F') *
      (τ : Matrix (Fin 3) (Fin 3) F') = 1 := by
    rw [← SpecialLinearGroup.coe_mul, inv_mul_cancel, SpecialLinearGroup.coe_one]
  obtain ⟨γ, β, α, s, hid⟩ := Model3LinOpp.key_exists _ _ hTT hTiT h₁ h₂ c
  obtain ⟨u, hu⟩ : ∃ u : SpecialLinearGroup (Fin 3) F',
      (u : Matrix (Fin 3) (Fin 3) F') = Model3LinOpp.uMat γ β α :=
    ⟨⟨_, Model3LinOpp.uMat_det γ β α⟩, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : SpecialLinearGroup (Fin 3) F',
      (Y : Matrix (Fin 3) (Fin 3) F') = transvection (0 : Fin 3) 2 s :=
    ⟨⟨_, Model3LinOpp.transv_det s⟩, rfl⟩
  have huU : u ∈ unitriangular 3 F' := by
    have hueq : u = ⟨Model3LinOpp.uMat γ β α, Model3LinOpp.uMat_det γ β α⟩ := Subtype.ext hu
    rw [hueq]
    exact Model3LinOpp.uMat_mem γ β α
  have hYU : Y ∈ unitriangular 3 F' := by
    have hYeq : Y = ⟨transvection (0 : Fin 3) 2 s, Model3LinOpp.transv_det s⟩ := Subtype.ext hY
    rw [hYeq]
    exact Model3LinOpp.transv_mem s
  have hAu : A * u = u * (τ⁻¹ * Y * τ) := by
    apply Subtype.ext
    simp only [SpecialLinearGroup.coe_mul]
    rw [hA, hu, hY]
    exact hid
  have hXU : τ⁻¹ * Y * τ ∈ (unitriangular 3 F').map (MulAut.conj τ⁻¹).toMonoidHom := by
    refine Subgroup.mem_map.mpr ⟨Y, hYU, ?_⟩
    show τ⁻¹ * Y * (τ⁻¹)⁻¹ = τ⁻¹ * Y * τ
    rw [inv_inv]
  have hA_eq : A = u * (τ⁻¹ * Y * τ) * u⁻¹ := by
    rw [← hAu, mul_inv_cancel_right]
  rw [hA_eq]
  exact mul_mem (mul_mem (Subgroup.mem_sup_left huU) (Subgroup.mem_sup_right hXU))
    (inv_mem (Subgroup.mem_sup_left huU))

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard
