module

public import Mathlib.Algebra.Field.ZMod
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.GraphAutomorphism

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix

@[expose] def W183PglKlein (x y : GL (Fin 3) (ZMod 2)) : Prop :=
  x ≠ 1 ∧ y ≠ 1 ∧ x ≠ y ∧ x * x = 1 ∧ y * y = 1 ∧ x * y = y * x

abbrev w183PglTau : GL (Fin 3) (ZMod 2) ≃* GL (Fin 3) (ZMod 2) :=
  Matrix.GeneralLinearGroup.inverseTranspose

@[expose] def W183PglAxis (x y : GL (Fin 3) (ZMod 2)) : Prop :=
  ∃ f u u' : Fin 3 → ZMod 2, f ≠ 0 ∧ u ≠ 0 ∧ u' ≠ 0 ∧ u ≠ u' ∧ f ⬝ᵥ u = 0 ∧ f ⬝ᵥ u' = 0 ∧
    (x : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 + vecMulVec u f ∧
      (y : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 + vecMulVec u' f

private abbrev w183PglM3 : Type := Matrix (Fin 3) (Fin 3) (ZMod 2)

private def w183PglKp (x y : w183PglM3) : Prop :=
  x * x = 1 ∧ y * y = 1 ∧ x ≠ 1 ∧ y ≠ 1 ∧ x ≠ y ∧ x * y = y * x

private instance (x y : w183PglM3) : Decidable (w183PglKp x y) := by
  unfold w183PglKp
  infer_instance

private def w183PglAx (x y : w183PglM3) : Prop :=
  ∃ f u u' : Fin 3 → ZMod 2, f ≠ 0 ∧ u ≠ 0 ∧ u' ≠ 0 ∧ u ≠ u' ∧ f ⬝ᵥ u = 0 ∧ f ⬝ᵥ u' = 0 ∧
    x = 1 + vecMulVec u f ∧ y = 1 + vecMulVec u' f

private instance (x y : w183PglM3) : Decidable (w183PglAx x y) := by
  unfold w183PglAx
  infer_instance

private theorem w183Pgl_klein_mat : ∀ x y : w183PglM3, w183PglKp x y →
    w183PglAx x y ∨ w183PglAx xᵀ yᵀ := by
  decide +kernel

private theorem w183Pgl_kp_of_klein {x y : GL (Fin 3) (ZMod 2)} (h : W183PglKlein x y) :
    w183PglKp (x : w183PglM3) (y : w183PglM3) := by
  obtain ⟨hx1, hy1, hxy, hx2, hy2, hc⟩ := h
  refine ⟨?_, ?_, fun h => hx1 (Units.ext h), fun h => hy1 (Units.ext h),
    fun h => hxy (Units.ext h), ?_⟩
  · simpa using congrArg (fun g : GL (Fin 3) (ZMod 2) => (g : w183PglM3)) hx2
  · simpa using congrArg (fun g : GL (Fin 3) (ZMod 2) => (g : w183PglM3)) hy2
  · simpa using congrArg (fun g : GL (Fin 3) (ZMod 2) => (g : w183PglM3)) hc

theorem w183Pgl_axis_or_centre {x y : GL (Fin 3) (ZMod 2)} (h : W183PglKlein x y) :
    W183PglAxis x y ∨ W183PglAxis (w183PglTau x) (w183PglTau y) := by
  obtain ⟨f, u, u', h1, h2, h3, h4, h5, h6, h7, h8⟩ |
      ⟨f, u, u', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    w183Pgl_klein_mat _ _ (w183Pgl_kp_of_klein h)
  · exact Or.inl ⟨f, u, u', h1, h2, h3, h4, h5, h6, h7, h8⟩
  · have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right h.2.2.2.1
    have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right h.2.2.2.2.1
    refine Or.inr ⟨f, u, u', h1, h2, h3, h4, h5, h6, ?_, ?_⟩
    · rw [Matrix.GeneralLinearGroup.coe_inverseTranspose, hxi]
      exact h7
    · rw [Matrix.GeneralLinearGroup.coe_inverseTranspose, hyi]
      exact h8

theorem w183Pgl_axis_conj {x y : GL (Fin 3) (ZMod 2)} (h : W183PglAxis x y)
    (c : GL (Fin 3) (ZMod 2)) : W183PglAxis (c * x * c⁻¹) (c * y * c⁻¹) := by
  obtain ⟨f, u, u', hf, hu, hu', huu', hfu, hfu', hx, hy⟩ := h
  have hcc : (c : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
      ((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 := Units.mul_inv c
  have hcc' : ((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
      (c : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 := Units.inv_mul c
  have hinj : ∀ v : Fin 3 → ZMod 2,
      (c : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v = 0 → v = 0 := fun v hv => by
    have := congrArg (fun w => ((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ w)
      hv
    simpa [Matrix.mulVec_mulVec, hcc'] using this
  have hinjl : ∀ v : Fin 3 → ZMod 2,
      v ᵥ* ((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 0 → v = 0 :=
    fun v hv => by
    have := congrArg (fun w => w ᵥ* (c : Matrix (Fin 3) (Fin 3) (ZMod 2))) hv
    simpa [Matrix.vecMul_vecMul, hcc'] using this
  have hdot : ∀ v w : Fin 3 → ZMod 2,
      (v ᵥ* ((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))) ⬝ᵥ
        ((c : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ w) = v ⬝ᵥ w := fun v w => by
    rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hcc', Matrix.one_mulVec]
  have hconj : ∀ u₁ : Fin 3 → ZMod 2,
      (c : Matrix (Fin 3) (Fin 3) (ZMod 2)) * (1 + vecMulVec u₁ f) *
        ((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      1 + vecMulVec ((c : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ u₁)
        (f ᵥ* ((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))) := fun u₁ => by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hcc, Matrix.mul_vecMulVec,
      Matrix.vecMulVec_mul]
  refine ⟨f ᵥ* ((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)),
    (c : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ u, (c : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ u',
    fun h0 => hf (hinjl f h0), fun h0 => hu (hinj u h0), fun h0 => hu' (hinj u' h0),
    fun h0 => huu' ?_, by rw [hdot, hfu], by rw [hdot, hfu'], ?_, ?_⟩
  · have h1 := congrArg (fun w =>
      ((c⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ w) h0
    simpa [Matrix.mulVec_mulVec, hcc'] using h1
  · rw [Units.val_mul, Units.val_mul, hx, hconj]
  · rw [Units.val_mul, Units.val_mul, hy, hconj]

set_option synthInstance.maxSize 4096 in
private theorem w183Pgl_axis_klein_mat : ∀ f u u' : Fin 3 → ZMod 2, f ≠ 0 → u ≠ 0 → u' ≠ 0 →
    u ≠ u' → f ⬝ᵥ u = 0 → f ⬝ᵥ u' = 0 →
    (1 + vecMulVec u f : w183PglM3) ≠ 1 ∧ (1 + vecMulVec u' f : w183PglM3) ≠ 1 ∧
    (1 + vecMulVec u f : w183PglM3) ≠ 1 + vecMulVec u' f ∧
    (1 + vecMulVec u f : w183PglM3) * (1 + vecMulVec u f) = 1 ∧
    (1 + vecMulVec u' f : w183PglM3) * (1 + vecMulVec u' f) = 1 ∧
    (1 + vecMulVec u f : w183PglM3) * (1 + vecMulVec u' f) =
      (1 + vecMulVec u' f) * (1 + vecMulVec u f) := by
  decide +kernel

theorem w183Pgl_axis_klein {x y : GL (Fin 3) (ZMod 2)} (h : W183PglAxis x y) :
    W183PglKlein x y := by
  obtain ⟨f, u, u', hf, hu, hu', huu', hfu, hfu', hx, hy⟩ := h
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := w183Pgl_axis_klein_mat f u u' hf hu hu' huu' hfu hfu'
  refine ⟨fun h => k1 (by rw [← hx, h]; rfl), fun h => k2 (by rw [← hy, h]; rfl),
    fun h => k3 (by rw [← hx, ← hy, h]), ?_, ?_, ?_⟩
  · apply Units.ext
    rw [Units.val_mul, hx, k4]
    rfl
  · apply Units.ext
    rw [Units.val_mul, hy, k5]
    rfl
  · apply Units.ext
    rw [Units.val_mul, Units.val_mul, hx, hy, k6]

private theorem w183Pgl_transvection_det :
    ∀ u f : Fin 3 → ZMod 2, f ⬝ᵥ u = 0 → (1 + vecMulVec u f : w183PglM3).det ≠ 0 := by
  decide +kernel

theorem w183Pgl_transvection_exists (u f : Fin 3 → ZMod 2) (h : f ⬝ᵥ u = 0) :
    ∃ t : GL (Fin 3) (ZMod 2), (t : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 + vecMulVec u f :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ (w183Pgl_transvection_det u f h),
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _⟩

set_option synthInstance.maxSize 4096 in
private theorem w183Pgl_flag_mat : ∀ u f : Fin 3 → ZMod 2, u ≠ 0 → f ≠ 0 → f ⬝ᵥ u = 0 →
    ∀ u₁ f₁ : Fin 3 → ZMod 2, u₁ ≠ 0 → f₁ ≠ 0 → f₁ ⬝ᵥ u₁ = 0 →
    ∃ s : w183PglM3, s.det ≠ 0 ∧ s *ᵥ u = u₁ ∧ f₁ ᵥ* s = f := by
  decide +kernel

theorem w183Pgl_flag_transitive {u f u₁ f₁ : Fin 3 → ZMod 2} (hu : u ≠ 0) (hf : f ≠ 0)
    (huf : f ⬝ᵥ u = 0) (hu₁ : u₁ ≠ 0) (hf₁ : f₁ ≠ 0) (huf₁ : f₁ ⬝ᵥ u₁ = 0) :
    ∃ g : GL (Fin 3) (ZMod 2), (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ u = u₁ ∧
      f ᵥ* ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = f₁ := by
  obtain ⟨s, hs, hsu, hsf⟩ := w183Pgl_flag_mat u f hu hf huf u₁ f₁ hu₁ hf₁ huf₁
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero s hs, ?_, ?_⟩
  · rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
    exact hsu
  · rw [← hsf, Matrix.vecMul_vecMul]
    have := Units.mul_inv (Matrix.GeneralLinearGroup.mkOfDetNeZero s hs)
    rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero] at this
    rw [this, Matrix.vecMul_one]

set_option synthInstance.maxSize 4096 in
private theorem w183Pgl_ker_span_vec : ∀ f u u' : Fin 3 → ZMod 2, f ≠ 0 → u ≠ 0 → u' ≠ 0 →
    u ≠ u' → f ⬝ᵥ u = 0 → f ⬝ᵥ u' = 0 →
      ∀ v : Fin 3 → ZMod 2, f ⬝ᵥ v = 0 → v = 0 ∨ v = u ∨ v = u' ∨ v = u + u' := by
  decide +kernel

theorem w183Pgl_ker_span {f u u' : Fin 3 → ZMod 2} (hf : f ≠ 0) (hu : u ≠ 0) (hu' : u' ≠ 0)
    (huu' : u ≠ u') (hfu : f ⬝ᵥ u = 0) (hfu' : f ⬝ᵥ u' = 0) {v : Fin 3 → ZMod 2}
    (hv : f ⬝ᵥ v = 0) : v = 0 ∨ v = u ∨ v = u' ∨ v = u + u' :=
  w183Pgl_ker_span_vec f u u' hf hu hu' huu' hfu hfu' v hv

set_option synthInstance.maxSize 4096 in
private theorem w183Pgl_nonzero_mat : ∀ v w : Fin 3 → ZMod 2, v ≠ 0 → w ≠ 0 →
    ∃ s : w183PglM3, s.det ≠ 0 ∧ s *ᵥ v = w := by
  decide +kernel

theorem w183Pgl_transitive_nonzero {v w : Fin 3 → ZMod 2} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ g : GL (Fin 3) (ZMod 2), (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v = w := by
  obtain ⟨s, hs, hsv⟩ := w183Pgl_nonzero_mat v w hv hw
  exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero s hs, by
    rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
    exact hsv⟩

set_option synthInstance.maxSize 4096 in
private theorem w183Pgl_adj_mat : ∀ x : w183PglM3, x * x = 1 → x ≠ 1 → ∀ y : w183PglM3,
    y * y = 1 → y ≠ 1 → x ≠ y → x * y = y * x → ∃ X : w183PglM3, Matrix.trace X = 0 ∧
      y * (x * X * x - X) * y ≠ x * X * x - X := by
  decide +kernel

theorem w183Pgl_adj_not_quadratic {x y : GL (Fin 3) (ZMod 2)} (h : W183PglKlein x y) :
    ∃ X : Matrix (Fin 3) (Fin 3) (ZMod 2), Matrix.trace X = 0 ∧
      (y : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
          ((x : Matrix (Fin 3) (Fin 3) (ZMod 2)) * X *
              ((x⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) - X) *
            ((y⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) ≠
        (x : Matrix (Fin 3) (Fin 3) (ZMod 2)) * X *
            ((x⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) - X := by
  obtain ⟨hx1, hy1, hxy, hx2, hy2, hc⟩ := h
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  rw [hxi, hyi]
  obtain ⟨hk1, hk2, hk3, hk4, hk5, hk6⟩ := w183Pgl_kp_of_klein ⟨hx1, hy1, hxy, hx2, hy2, hc⟩
  exact w183Pgl_adj_mat _ hk1 hk3 _ hk2 hk4 hk5 hk6

end CFSG.LocalAnalysis.WeakClosure81

end
