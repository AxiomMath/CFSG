module

public import CFSG.LocalAnalysis.WeakClosure81.SevenNineOrthModel
public import CFSG.LocalAnalysis.WeakClosure81.SevenNineOrthFrameFive

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix CFSG.Quasithin CFSG.Open

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace OrthFrameFive

private theorem mul_self_ne_two : ∀ c : ZMod 5, c * c ≠ 2 := by decide

private theorem neg_two_ne_zero : (-2 : ZMod 5) ≠ 0 := by decide

private theorem norm_v_num :
    (2 : ZMod 5) * ((2 : ZMod 5) * (-2) + 0) + ((2 : ZMod 5) * 0 + 1) = -2 := by decide

private theorem pair_a_v_num : (2 : ZMod 5) * (-2) + 0 ≠ 0 := by decide

private theorem pair_b_v_num : (2 : ZMod 5) * 0 + 1 ≠ 0 := by decide

private theorem inv_two : (2 : ZMod 5)⁻¹ = 3 := by
  apply inv_eq_of_mul_eq_one_right
  decide

private theorem two_ne_zero' : (2 : ZMod 5) ≠ 0 := by decide

private theorem three_ne_zero' : (3 : ZMod 5) ≠ 0 := by decide

private theorem four_ne_zero' : (4 : ZMod 5) ≠ 0 := by decide

private theorem norm_x1_num :
    (0 : ZMod 5) + 4 * 1 + 4 * (1 + 4 * 0) = -2 := by decide

private theorem norm_x2_num :
    (0 : ZMod 5) + 2 * 1 + 3 * 0 + 2 * (1 + 2 * 0 + 3 * 0) + 3 * (0 + 2 * 0 + 3 * 1) = -2 := by
  decide

private theorem norm_x3_num :
    (2 : ZMod 5) * (2 * 0 + 2 * 1) + 2 * (2 * 1 + 2 * 0) = -2 := by decide

private theorem norm_x4_num :
    (2 : ZMod 5) * (2 * 0 + 3 * 1 + 0) + 3 * (2 * 1 + 3 * 0 + 0) + (2 * 0 + 3 * 0 + 1) = -2 := by
  decide

private theorem gram_x4_x3_num :
    (2 : ZMod 5) * (2 * 0 + 3 * 1 + 0) + 2 * (2 * 1 + 3 * 0 + 0) = 0 := by decide

private theorem gram_x4_x2_num :
    (2 : ZMod 5) * 0 + 3 * 1 + 0 + 2 * (2 * 1 + 3 * 0 + 0) + 3 * (2 * 0 + 3 * 0 + 1) = 0 := by
  decide

private theorem gram_x4_x1_num :
    (2 : ZMod 5) * 0 + 3 * 1 + 0 + 4 * (2 * 1 + 3 * 0 + 0) = 1 := by decide

private theorem gram_x3_x2_num :
    (2 : ZMod 5) * 0 + 2 * 1 + 2 * (2 * 1 + 2 * 0) + 3 * (2 * 0 + 2 * 0) = 1 := by decide

private theorem gram_x3_x1_num :
    (2 : ZMod 5) * 0 + 2 * 1 + 4 * (2 * 1 + 2 * 0) = 0 := by decide

private theorem gram_x2_x1_num :
    (0 : ZMod 5) + 2 * 1 + 3 * 0 + 4 * (1 + 2 * 0 + 3 * 0) = 1 := by decide

private theorem coeff_e1 (α β γ : ZMod 5) :
    α + 4 * β + (2 * α + 3 * β + γ) + (3 * α + 4 * β + 3 * γ) = α + β + 4 * γ := by
  revert α β γ
  decide

private theorem coeff_b (α β γ : ZMod 5) :
    (2 * α + 3 * β + γ) + 3 * (3 * α + 4 * β + 3 * γ) = α := by
  revert α β γ
  decide

private theorem coeff_s (α β γ : ZMod 5) :
    2 * (2 * α + 3 * β + γ) + 2 * (2 * α + 2 * β) + (3 * α + 4 * β + 3 * γ) + (α + β + 4 * γ)
      = 2 * α + 4 * γ := by
  revert α β γ
  decide

private theorem coeff_s' (α β γ : ZMod 5) :
    3 * (2 * α + 3 * β + γ) + 2 * (2 * α + 2 * β) + 2 * (3 * α + 4 * β + 3 * γ)
      + 4 * (α + β + 4 * γ) = 0 := by
  revert α β γ
  decide

private theorem coeff_s_eq (α γ : ZMod 5) : 2 * α + 4 * γ = -γ - 3 * α := by
  revert α γ
  decide

variable [Fact (Nat.Prime 5)] {f : LinearMap.BilinForm (ZMod 5) (Fin 4 → ZMod 5)}
  (F : OrthFrameFive f)

private theorem a_orth_b : f F.a F.b = 0 := by rw [F.symm, F.b_orth_a]

private theorem v_mem_U : (2 : ZMod 5) • F.a + F.b ∈ F.U :=
  F.U.add_mem (F.U.smul_mem 2 F.a_mem_U) (F.mem_U.2 ⟨F.b_orth_s, F.b_orth_s'⟩)

private theorem norm_v : f ((2 : ZMod 5) • F.a + F.b) ((2 : ZMod 5) • F.a + F.b) = -2 := by
  simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left,
    LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right, F.norm_a, F.norm_b,
    F.b_orth_a, F.a_orth_b]
  exact norm_v_num

private theorem pair_a_v : f F.a ((2 : ZMod 5) • F.a + F.b) ≠ 0 := by
  simp only [LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right, F.norm_a,
    F.a_orth_b]
  exact pair_a_v_num

private theorem pair_b_v : f F.b ((2 : ZMod 5) • F.a + F.b) ≠ 0 := by
  simp only [LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right, F.b_orth_a,
    F.norm_b]
  exact pair_b_v_num

theorem span_le :
    F.U ≤ Submodule.span (ZMod 5) {v | v ∈ F.U ∧ f v v = -2 ∧ f F.a v ≠ 0} := by
  intro w hw
  have hws : f w F.s = 0 := (F.mem_U.1 hw).1
  have hws' : f w F.s' = 0 := (F.mem_U.1 hw).2
  have ha : F.a ∈ Submodule.span (ZMod 5) {v | v ∈ F.U ∧ f v v = -2 ∧ f F.a v ≠ 0} :=
    Submodule.subset_span ⟨F.a_mem_U, F.norm_a, by rw [F.norm_a]; exact neg_two_ne_zero⟩
  have hv : (2 : ZMod 5) • F.a + F.b ∈
      Submodule.span (ZMod 5) {v | v ∈ F.U ∧ f v v = -2 ∧ f F.a v ≠ 0} :=
    Submodule.subset_span ⟨F.v_mem_U, F.norm_v, F.pair_a_v⟩
  have hb : F.b ∈ Submodule.span (ZMod 5) {v | v ∈ F.U ∧ f v v = -2 ∧ f F.a v ≠ 0} := by
    have h : F.b = ((2 : ZMod 5) • F.a + F.b) - (2 : ZMod 5) • F.a := by abel
    rw [h]
    exact Submodule.sub_mem _ hv (Submodule.smul_mem _ _ ha)
  rw [F.span w hws hws']
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ ha) (Submodule.smul_mem _ _ hb)

theorem exists_vw :
    ∃ v w, v ∈ F.U ∧ f v v = -2 ∧ f F.a v ≠ 0 ∧ w ∈ F.U ∧ f w F.a = 0 ∧ f w v ≠ 0 :=
  ⟨(2 : ZMod 5) • F.a + F.b, F.b, F.v_mem_U, F.norm_v, F.pair_a_v,
    F.mem_U.2 ⟨F.b_orth_s, F.b_orth_s'⟩, F.b_orth_a, F.pair_b_v⟩

private theorem s'_orth_s : f F.s' F.s = 1 := by rw [F.symm, F.pair]

private theorem s_orth_b : f F.s F.b = 0 := by rw [F.symm, F.b_orth_s]

private theorem s'_orth_b : f F.s' F.b = 0 := by rw [F.symm, F.b_orth_s']

private theorem norm_x1 :
    f (F.s + (4 : ZMod 5) • F.s') (F.s + (4 : ZMod 5) • F.s') = -2 := by
  simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left,
    LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right, F.isotropic_s,
    F.isotropic_s', F.pair, F.s'_orth_s]
  exact norm_x1_num

private theorem norm_x2 :
    f (F.s + (2 : ZMod 5) • F.s' + (3 : ZMod 5) • F.b)
      (F.s + (2 : ZMod 5) • F.s' + (3 : ZMod 5) • F.b) = -2 := by
  simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left,
    LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right, F.isotropic_s,
    F.isotropic_s', F.pair, F.norm_b, F.s'_orth_s, F.s'_orth_b, F.s_orth_b, F.b_orth_s, F.b_orth_s']
  exact norm_x2_num

private theorem norm_x3 :
    f ((2 : ZMod 5) • F.s + (2 : ZMod 5) • F.s') ((2 : ZMod 5) • F.s + (2 : ZMod 5) • F.s') =
      -2 := by
  simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left,
    LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right, F.isotropic_s,
    F.isotropic_s', F.pair, F.s'_orth_s]
  exact norm_x3_num

private theorem norm_x4 :
    f ((2 : ZMod 5) • F.s + (3 : ZMod 5) • F.s' + F.b)
      ((2 : ZMod 5) • F.s + (3 : ZMod 5) • F.s' + F.b) = -2 := by
  simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left,
    LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right, F.isotropic_s,
    F.isotropic_s', F.pair, F.norm_b, F.s'_orth_s, F.s'_orth_b, F.s_orth_b, F.b_orth_s, F.b_orth_s']
  exact norm_x4_num

private theorem gram_x4_x3 :
    f ((2 : ZMod 5) • F.s + (3 : ZMod 5) • F.s' + F.b)
      ((2 : ZMod 5) • F.s + (2 : ZMod 5) • F.s') = 0 := by
  simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left,
    LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right, F.isotropic_s,
    F.isotropic_s', F.pair, F.s'_orth_s, F.b_orth_s, F.b_orth_s']
  exact gram_x4_x3_num

private theorem gram_x4_x2 :
    f ((2 : ZMod 5) • F.s + (3 : ZMod 5) • F.s' + F.b)
      (F.s + (2 : ZMod 5) • F.s' + (3 : ZMod 5) • F.b) = 0 := by
  simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left,
    LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right, F.isotropic_s,
    F.isotropic_s', F.pair, F.norm_b, F.s'_orth_s, F.s'_orth_b, F.s_orth_b, F.b_orth_s, F.b_orth_s']
  exact gram_x4_x2_num

private theorem gram_x4_x1 :
    f ((2 : ZMod 5) • F.s + (3 : ZMod 5) • F.s' + F.b) (F.s + (4 : ZMod 5) • F.s') = 1 := by
  simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left,
    LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right, F.isotropic_s,
    F.isotropic_s', F.pair, F.s'_orth_s, F.b_orth_s, F.b_orth_s']
  exact gram_x4_x1_num

private theorem gram_x3_x2 :
    f ((2 : ZMod 5) • F.s + (2 : ZMod 5) • F.s')
      (F.s + (2 : ZMod 5) • F.s' + (3 : ZMod 5) • F.b) = 1 := by
  simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left,
    LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right, F.isotropic_s,
    F.isotropic_s', F.pair, F.s'_orth_s, F.s'_orth_b, F.s_orth_b]
  exact gram_x3_x2_num

private theorem gram_x3_x1 :
    f ((2 : ZMod 5) • F.s + (2 : ZMod 5) • F.s') (F.s + (4 : ZMod 5) • F.s') = 0 := by
  simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left,
    LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right, F.isotropic_s,
    F.isotropic_s', F.pair, F.s'_orth_s]
  exact gram_x3_x1_num

private theorem gram_x2_x1 :
    f (F.s + (2 : ZMod 5) • F.s' + (3 : ZMod 5) • F.b) (F.s + (4 : ZMod 5) • F.s') = 1 := by
  simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left,
    LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right, F.isotropic_s,
    F.isotropic_s', F.pair, F.s'_orth_s, F.b_orth_s, F.b_orth_s']
  exact gram_x2_x1_num

private theorem f_y_x1 (y : Fin 4 → ZMod 5) :
    f y (F.s + (4 : ZMod 5) • F.s') = f y F.s + 4 * f y F.s' := by
  simp only [LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right]

private theorem f_y_x2 (y : Fin 4 → ZMod 5) :
    f y (F.s + (2 : ZMod 5) • F.s' + (3 : ZMod 5) • F.b) =
      f y F.s + 2 * f y F.s' + 3 * f y F.b := by
  simp only [LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right]

private theorem f_y_x3 (y : Fin 4 → ZMod 5) :
    f y ((2 : ZMod 5) • F.s + (2 : ZMod 5) • F.s') = 2 * f y F.s + 2 * f y F.s' := by
  simp only [LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right]

private theorem f_y_x4 (y : Fin 4 → ZMod 5) :
    f y ((2 : ZMod 5) • F.s + (3 : ZMod 5) • F.s' + F.b) =
      2 * f y F.s + 3 * f y F.s' + f y F.b := by
  simp only [LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right]

private theorem refl_x4_apply (y : Fin 4 → ZMod 5) :
    (orthRefl f ((2 : ZMod 5) • F.s + (3 : ZMod 5) • F.s' + F.b) :
        Matrix (Fin 4) (Fin 4) (ZMod 5)) *ᵥ y =
      y + (2 * f y F.s + 3 * f y F.s' + f y F.b) •
        ((2 : ZMod 5) • F.s + (3 : ZMod 5) • F.s' + F.b) := by
  rw [orthRefl_mulVec f F.norm_x4, F.f_y_x4 y]

private theorem f_step_x3 (y : Fin 4 → ZMod 5) :
    f (y + (2 * f y F.s + 3 * f y F.s' + f y F.b) •
        ((2 : ZMod 5) • F.s + (3 : ZMod 5) • F.s' + F.b))
      ((2 : ZMod 5) • F.s + (2 : ZMod 5) • F.s') = 2 * f y F.s + 2 * f y F.s' := by
  rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, F.f_y_x3 y,
    F.gram_x4_x3, mul_zero, add_zero]

private theorem refl_x3_apply (y : Fin 4 → ZMod 5) :
    (orthRefl f ((2 : ZMod 5) • F.s + (2 : ZMod 5) • F.s') :
        Matrix (Fin 4) (Fin 4) (ZMod 5)) *ᵥ
      (y + (2 * f y F.s + 3 * f y F.s' + f y F.b) •
        ((2 : ZMod 5) • F.s + (3 : ZMod 5) • F.s' + F.b)) =
      (y + (2 * f y F.s + 3 * f y F.s' + f y F.b) •
        ((2 : ZMod 5) • F.s + (3 : ZMod 5) • F.s' + F.b)) +
        (2 * f y F.s + 2 * f y F.s') •
          ((2 : ZMod 5) • F.s + (2 : ZMod 5) • F.s') := by
  rw [orthRefl_mulVec f F.norm_x3, F.f_step_x3 y]

private theorem f_step_x2 (y : Fin 4 → ZMod 5) :
    f (y + (2 * f y F.s + 3 * f y F.s' + f y F.b) •
          ((2 : ZMod 5) • F.s + (3 : ZMod 5) • F.s' + F.b)
        + (2 * f y F.s + 2 * f y F.s') • ((2 : ZMod 5) • F.s + (2 : ZMod 5) • F.s'))
      (F.s + (2 : ZMod 5) • F.s' + (3 : ZMod 5) • F.b) =
      3 * f y F.s + 4 * f y F.s' + 3 * f y F.b := by
  rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_left,
    LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_left, F.f_y_x2 y,
    F.gram_x4_x2, F.gram_x3_x2, mul_zero, mul_one, add_zero]
  ring

private theorem refl_x2_apply (y : Fin 4 → ZMod 5) :
    (orthRefl f (F.s + (2 : ZMod 5) • F.s' + (3 : ZMod 5) • F.b) :
        Matrix (Fin 4) (Fin 4) (ZMod 5)) *ᵥ
      (y + (2 * f y F.s + 3 * f y F.s' + f y F.b) •
          ((2 : ZMod 5) • F.s + (3 : ZMod 5) • F.s' + F.b)
        + (2 * f y F.s + 2 * f y F.s') • ((2 : ZMod 5) • F.s + (2 : ZMod 5) • F.s')) =
      (y + (2 * f y F.s + 3 * f y F.s' + f y F.b) •
          ((2 : ZMod 5) • F.s + (3 : ZMod 5) • F.s' + F.b)
        + (2 * f y F.s + 2 * f y F.s') • ((2 : ZMod 5) • F.s + (2 : ZMod 5) • F.s')) +
        (3 * f y F.s + 4 * f y F.s' + 3 * f y F.b) •
          (F.s + (2 : ZMod 5) • F.s' + (3 : ZMod 5) • F.b) := by
  rw [orthRefl_mulVec f F.norm_x2, F.f_step_x2 y]

private theorem f_step_x1 (y : Fin 4 → ZMod 5) :
    f (y + (2 * f y F.s + 3 * f y F.s' + f y F.b) •
          ((2 : ZMod 5) • F.s + (3 : ZMod 5) • F.s' + F.b)
        + (2 * f y F.s + 2 * f y F.s') • ((2 : ZMod 5) • F.s + (2 : ZMod 5) • F.s')
        + (3 * f y F.s + 4 * f y F.s' + 3 * f y F.b) •
          (F.s + (2 : ZMod 5) • F.s' + (3 : ZMod 5) • F.b))
      (F.s + (4 : ZMod 5) • F.s') = f y F.s + f y F.s' + 4 * f y F.b := by
  rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_left,
    LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left,
    LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_left, F.f_y_x1 y,
    F.gram_x4_x1, F.gram_x3_x1, F.gram_x2_x1]
  simp only [mul_one, mul_zero, add_zero]
  exact coeff_e1 (f y F.s) (f y F.s') (f y F.b)

private theorem refl_x1_apply (y : Fin 4 → ZMod 5) :
    (orthRefl f (F.s + (4 : ZMod 5) • F.s') :
        Matrix (Fin 4) (Fin 4) (ZMod 5)) *ᵥ
      (y + (2 * f y F.s + 3 * f y F.s' + f y F.b) •
          ((2 : ZMod 5) • F.s + (3 : ZMod 5) • F.s' + F.b)
        + (2 * f y F.s + 2 * f y F.s') • ((2 : ZMod 5) • F.s + (2 : ZMod 5) • F.s')
        + (3 * f y F.s + 4 * f y F.s' + 3 * f y F.b) •
          (F.s + (2 : ZMod 5) • F.s' + (3 : ZMod 5) • F.b)) =
      (y + (2 * f y F.s + 3 * f y F.s' + f y F.b) •
          ((2 : ZMod 5) • F.s + (3 : ZMod 5) • F.s' + F.b)
        + (2 * f y F.s + 2 * f y F.s') • ((2 : ZMod 5) • F.s + (2 : ZMod 5) • F.s')
        + (3 * f y F.s + 4 * f y F.s' + 3 * f y F.b) •
          (F.s + (2 : ZMod 5) • F.s' + (3 : ZMod 5) • F.b)) +
        (f y F.s + f y F.s' + 4 * f y F.b) • (F.s + (4 : ZMod 5) • F.s') := by
  rw [orthRefl_mulVec f F.norm_x1, F.f_step_x1 y]

theorem siegel_b_eq :
    F.siegel F.b =
      orthRefl f (F.s + (4 : ZMod 5) • F.s') *
        orthRefl f (F.s + (2 : ZMod 5) • F.s' + (3 : ZMod 5) • F.b) *
        orthRefl f ((2 : ZMod 5) • F.s + (2 : ZMod 5) • F.s') *
        orthRefl f ((2 : ZMod 5) • F.s + (3 : ZMod 5) • F.s' + F.b) := by
  apply gl_ext_mulVec
  intro y
  rw [F.siegel_mulVec F.b_orth_s, inv_two, F.norm_b, mul_one]
  simp only [Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]
  rw [F.refl_x4_apply y, F.refl_x3_apply y, F.refl_x2_apply y, F.refl_x1_apply y]
  set α : ZMod 5 := f y F.s with hα
  set β : ZMod 5 := f y F.s' with hβ
  set γ : ZMod 5 := f y F.b with hγ
  set e4 : ZMod 5 := 2 * α + 3 * β + γ with he4
  set e3 : ZMod 5 := 2 * α + 2 * β with he3
  set e2 : ZMod 5 := 3 * α + 4 * β + 3 * γ with he2
  set e1 : ZMod 5 := α + β + 4 * γ with he1
  set x1 : Fin 4 → ZMod 5 := F.s + (4 : ZMod 5) • F.s' with hx1
  set x2 : Fin 4 → ZMod 5 := F.s + (2 : ZMod 5) • F.s' + (3 : ZMod 5) • F.b with hx2
  set x3 : Fin 4 → ZMod 5 := (2 : ZMod 5) • F.s + (2 : ZMod 5) • F.s' with hx3
  set x4 : Fin 4 → ZMod 5 := (2 : ZMod 5) • F.s + (3 : ZMod 5) • F.s' + F.b with hx4
  have hcollapse :
      y + e4 • x4 + e3 • x3 + e2 • x2 + e1 • x1 =
        y + (e4 + 3 * e2) • F.b + (2 * e4 + 2 * e3 + e2 + e1) • F.s
          + (3 * e4 + 2 * e3 + 2 * e2 + 4 * e1) • F.s' := by
    rw [hx4, hx3, hx2, hx1]
    module
  rw [hcollapse,
    show e4 + 3 * e2 = α by rw [he4, he2]; exact coeff_b α β γ,
    show 2 * e4 + 2 * e3 + e2 + e1 = 2 * α + 4 * γ by
      rw [he4, he3, he2, he1]; exact coeff_s α β γ,
    show 3 * e4 + 2 * e3 + 2 * e2 + 4 * e1 = 0 by
      rw [he4, he3, he2, he1]; exact coeff_s' α β γ]
  rw [zero_smul, add_zero, show 2 * α + 4 * γ = -γ - 3 * α from coeff_s_eq α γ]
  module

private theorem s_orth_a : f F.s F.a = 0 := by rw [F.symm, F.a_orth_s]

private theorem a_orth_x1 : f F.a (F.s + (4 : ZMod 5) • F.s') = 0 := by
  simp only [LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right,
    F.a_orth_s, F.a_orth_s', mul_zero, add_zero]

private theorem a_orth_x2 : f F.a (F.s + (2 : ZMod 5) • F.s' + (3 : ZMod 5) • F.b) = 0 := by
  simp only [LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right,
    F.a_orth_s, F.a_orth_s', F.a_orth_b, mul_zero, add_zero]

private theorem a_orth_x3 : f F.a ((2 : ZMod 5) • F.s + (2 : ZMod 5) • F.s') = 0 := by
  simp only [LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right,
    F.a_orth_s, F.a_orth_s', mul_zero, add_zero]

private theorem a_orth_x4 : f F.a ((2 : ZMod 5) • F.s + (3 : ZMod 5) • F.s' + F.b) = 0 := by
  simp only [LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right,
    F.a_orth_s, F.a_orth_s', F.a_orth_b, mul_zero, add_zero]

private theorem a_add_s_pair_x1 : f (F.a + F.s) (F.s + (4 : ZMod 5) • F.s') ≠ 0 := by
  have h : f (F.a + F.s) (F.s + (4 : ZMod 5) • F.s') = 4 := by
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_right, F.a_orth_s, F.a_orth_s', F.isotropic_s, F.pair,
      mul_one, add_zero, zero_add]
  rw [h]
  exact four_ne_zero'

private theorem a_add_s_pair_x2 :
    f (F.a + F.s) (F.s + (2 : ZMod 5) • F.s' + (3 : ZMod 5) • F.b) ≠ 0 := by
  have h : f (F.a + F.s) (F.s + (2 : ZMod 5) • F.s' + (3 : ZMod 5) • F.b) = 2 := by
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_right, F.a_orth_s, F.a_orth_s', F.a_orth_b, F.isotropic_s,
      F.pair, F.s_orth_b, mul_zero, mul_one, add_zero, zero_add]
  rw [h]
  exact two_ne_zero'

private theorem a_add_s_pair_x3 :
    f (F.a + F.s) ((2 : ZMod 5) • F.s + (2 : ZMod 5) • F.s') ≠ 0 := by
  have h : f (F.a + F.s) ((2 : ZMod 5) • F.s + (2 : ZMod 5) • F.s') = 2 := by
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_right, F.a_orth_s, F.a_orth_s', F.isotropic_s, F.pair,
      mul_zero, mul_one, add_zero, zero_add]
  rw [h]
  exact two_ne_zero'

private theorem a_add_s_pair_x4 :
    f (F.a + F.s) ((2 : ZMod 5) • F.s + (3 : ZMod 5) • F.s' + F.b) ≠ 0 := by
  have h : f (F.a + F.s) ((2 : ZMod 5) • F.s + (3 : ZMod 5) • F.s' + F.b) = 3 := by
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_right, F.a_orth_s, F.a_orth_s', F.a_orth_b, F.isotropic_s,
      F.pair, F.s_orth_b, mul_zero, mul_one, add_zero, zero_add]
  rw [h]
  exact three_ne_zero'

theorem siegel_mem_orthConjSup :
    ∀ w ∈ F.U, f w F.a = 0 → F.siegel w ∈ orthConjSup f F.a := by
  intro w hw hwa
  have hws : f w F.s = 0 := (F.mem_U.1 hw).1
  have hws' : f w F.s' = 0 := (F.mem_U.1 hw).2
  have hw' : w = f w F.b • F.b := by
    conv_lhs => rw [F.span w hws hws']
    rw [hwa, mul_zero, zero_smul, zero_add]
  have hnorm_pair : f (F.a + F.s) (F.a + F.s) = -2 := by
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      F.norm_a, F.a_orth_s, F.s_orth_a, F.isotropic_s, add_zero]
  have hpair_a : f F.a (F.a + F.s) ≠ 0 := by
    rw [LinearMap.BilinForm.add_right, F.norm_a, F.a_orth_s, add_zero]
    exact neg_two_ne_zero
  have key : ∀ x : Fin 4 → ZMod 5, f x x = -2 → f F.a x = 0 → f (F.a + F.s) x ≠ 0 →
      orthRefl f x ∈ orthConjSup f F.a := by
    intro x hx hxa hxas
    have h1 : OrthReflConj f F.a (F.a + F.s) :=
      orthReflConj_of_ne_zero f (Or.inr rfl) F.symm F.norm_a hnorm_pair hpair_a
    have h2 : OrthReflConj f (F.a + F.s) x :=
      orthReflConj_of_ne_zero f (Or.inr rfl) F.symm hnorm_pair hx hxas
    exact orthRefl_mem_orthConjSup f F.symm hxa (h1.trans h2)
  have hb : F.siegel F.b ∈ orthConjSup f F.a := by
    rw [siegel_b_eq]
    exact Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.mul_mem _
        (key _ F.norm_x1 F.a_orth_x1 F.a_add_s_pair_x1)
        (key _ F.norm_x2 F.a_orth_x2 F.a_add_s_pair_x2))
        (key _ F.norm_x3 F.a_orth_x3 F.a_add_s_pair_x3))
      (key _ F.norm_x4 F.a_orth_x4 F.a_add_s_pair_x4)
  have hsiegel : F.siegel w = F.siegel (f w F.b • F.b) := congrArg F.siegel hw'
  rw [hsiegel, ← ZMod.natCast_zmod_val (f w F.b), Nat.cast_smul_eq_nsmul, F.siegel_nsmul F.b_orth_s]
  exact Subgroup.pow_mem _ hb _

theorem sevenNineConfig :
    SevenNineConfig (Subgroup.closure (orthReflSet 5 4 f)) (Subgroup.zpowers F.refl) 5 F.Y F.Z :=
  F.toOrthFrame.sevenNineConfig_of_span mul_self_ne_two F.span_le F.exists_vw
    F.siegel_mem_orthConjSup

end OrthFrameFive

end CFSG.LocalAnalysis.WeakClosure81
