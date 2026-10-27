module

public import Mathlib.RingTheory.Trace.Basic

public section

namespace CFSG.StandardType.ClassicalPosition

private lemma ttAux_trace_ext {K A : Type} [Field K] [Field A] [Algebra K A]
    [FiniteDimensional K A] [Algebra.IsSeparable K A] {z z' : A}
    (h : ∀ c : A, Algebra.trace K A (c * z) = Algebra.trace K A (c * z')) : z = z' := by
  have hzero : ∀ c : A, Algebra.trace K A (c * (z - z')) = 0 := by
    intro c
    rw [mul_sub, map_sub, h c, sub_self]
  have hz : z - z' = 0 := by
    let D : A ≃ₗ[K] Module.Dual K A :=
      (Algebra.traceForm K A).toDual (traceForm_nondegenerate K A)
    have hD : D (z - z') = 0 := by
      ext c
      rw [LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply, mul_comm]
      exact hzero c
    exact D.injective (by rw [hD, map_zero])
  exact sub_eq_zero.mp hz

private lemma ttAux_trace_ringEquiv {K A : Type} [Field K] [Field A] [Algebra K A]
    (σ : K ≃+* K) (τ : A ≃+* A)
    (hτσ : ∀ c : K, τ (algebraMap K A c) = algebraMap K A (σ c)) (t : A) :
    σ (Algebra.trace K A t) = Algebra.trace K A (τ t) := by
  have he : (algebraMap K A).comp (σ : K →+* K) = (τ : A →+* A).comp (algebraMap K A) := by
    ext c
    exact (hτσ c).symm
  have h := Algebra.trace_eq_of_equiv_equiv (A₁ := K) (B₁ := A) (A₂ := K) (B₂ := A) σ τ he t
  rw [h]
  exact σ.apply_symm_apply _

theorem existsUnique_traceTransfer {K A W : Type} [Field K] [Field A] [Algebra K A]
    [FiniteDimensional K A] [Algebra.IsSeparable K A] [AddCommGroup W] [Module A W] [Module K W]
    [IsScalarTower K A W] (B : W → W →ₗ[K] K) (x : W) :
    ∃! hx : W →ₗ[A] A, ∀ (y : W) (c : A), B x (c • y) = Algebra.trace K A (c * hx y) := by
  let D : A ≃ₗ[K] Module.Dual K A :=
    (Algebra.traceForm K A).toDual (traceForm_nondegenerate K A)
  have D_apply : ∀ (z c : A), D z c = Algebra.trace K A (c * z) := by
    intro z c
    rw [LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply, mul_comm]
  let smulL : W → A →ₗ[K] W := fun y =>
    { toFun := fun c => c • y
      map_add' := by
        intro c c'
        rw [add_smul]
      map_smul' := by
        intro k c
        change (k • c) • y = k • (c • y)
        rw [smul_assoc] }
  have smulL_apply : ∀ (y : W) (c : A), smulL y c = c • y := fun _ _ => rfl
  let φ : W → A →ₗ[K] K := fun y => (B x).comp (smulL y)
  have φ_apply : ∀ (y : W) (c : A), φ y c = B x (c • y) := by
    intro y c
    simp only [φ, LinearMap.comp_apply, smulL_apply]
  have hmem : ∀ (y : W) (c : A),
      B x (c • y) = Algebra.trace K A (c * D.symm (φ y)) := by
    intro y c
    rw [← φ_apply y c, ← D_apply (D.symm (φ y)) c, LinearEquiv.apply_symm_apply]
  let hx : W →ₗ[A] A :=
    { toFun := fun y => D.symm (φ y)
      map_add' := by
        intro y y'
        apply D.injective
        rw [map_add]
        simp only [LinearEquiv.apply_symm_apply]
        ext c
        simp only [φ_apply, LinearMap.add_apply, smul_add, map_add]
      map_smul' := by
        intro a y
        apply D.injective
        simp only [LinearEquiv.apply_symm_apply]
        ext c
        calc
          φ (a • y) c = B x (c • (a • y)) := φ_apply (a • y) c
          _ = B x ((c * a) • y) := by rw [← smul_assoc, smul_eq_mul]
          _ = φ y (c * a) := (φ_apply y (c * a)).symm
          _ = (D (D.symm (φ y))) (c * a) := by rw [LinearEquiv.apply_symm_apply]
          _ = Algebra.trace K A ((c * a) * D.symm (φ y)) :=
                D_apply (D.symm (φ y)) (c * a)
          _ = Algebra.trace K A (c * (a * D.symm (φ y))) := by rw [mul_assoc]
          _ = Algebra.trace K A (c * (a • D.symm (φ y))) := rfl
          _ = (D (a • D.symm (φ y))) c := (D_apply (a • D.symm (φ y)) c).symm }
  have hx_spec : ∀ (y : W) (c : A), B x (c • y) = Algebra.trace K A (c * hx y) := by
    intro y c
    change B x (c • y) = Algebra.trace K A (c * D.symm (φ y))
    exact hmem y c
  exact ⟨hx, hx_spec, fun hy hhy => by
    ext y
    apply ttAux_trace_ext (K := K)
    intro c
    rw [← hhy y c, ← hx_spec y c]⟩

theorem traceTransfer_herm {K A W : Type} [Field K] [Field A] [Algebra K A]
    [FiniteDimensional K A] [Algebra.IsSeparable K A] [AddCommGroup W] [Module A W] [Module K W]
    (σ : K ≃+* K) (B : W → W →ₗ[K] K) (h : W → W →ₗ[A] A)
    (hB : ∀ (x y : W) (c : A), B x (c • y) = Algebra.trace K A (c * h x y))
    (hBh : ∀ x y, B y x = σ (B x y))
    (τ : A ≃+* A) (hτσ : ∀ c : K, τ (algebraMap K A c) = algebraMap K A (σ c))
    (hτ2 : ∀ a, τ (τ a) = a) (hτ : ∀ (a : A) (x y : W), B (a • x) y = B x (τ a • y)) :
    (∀ (a : A) (x y : W), h (a • x) y = τ a * h x y) ∧ ∀ x y, h y x = τ (h x y) := by
  constructor
  · intro a x y
    apply ttAux_trace_ext (K := K)
    intro c
    rw [← hB (a • x) y c, hτ a x (c • y), ← smul_assoc, hB x y (τ a • c)]
    congr 1
    change (τ a * c) * h x y = c * (τ a * h x y)
    ring
  · intro x y
    apply ttAux_trace_ext (K := K)
    intro c
    rw [← hB y x c, hBh (c • x) y, hτ c x y, hB x y (τ c)]
    rw [ttAux_trace_ringEquiv σ τ hτσ (τ c * h x y)]
    congr 1
    rw [map_mul, hτ2]

end CFSG.StandardType.ClassicalPosition
