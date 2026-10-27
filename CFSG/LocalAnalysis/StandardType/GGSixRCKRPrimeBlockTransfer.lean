module

public import Mathlib.LinearAlgebra.Matrix.ToLin

public section

namespace CFSG.StandardType.RCKRP

open scoped Matrix

private lemma rckRPbt_fix {ι F K W : Type} [Fintype ι] [DecidableEq ι] [Field F]
    [Field K] [Algebra F K] [AddCommGroup W] [Module F W] [Module K W] [IsScalarTower F K W]
    {e : Matrix ι ι F} (eW : W ≃ₗ[F] LinearMap.range (Matrix.toLin' e)) {x : Matrix ι ι F}
    {T : W →ₗ[K] W} (hT : ∀ w, x *ᵥ (eW w : ι → F) = (eW (T w) : ι → F)) (u : W) :
    Matrix.toLin' (x - 1) (((LinearMap.range (Matrix.toLin' e)).subtype ∘ₗ eW.toLinearMap) u) =
      ((LinearMap.range (Matrix.toLin' e)).subtype ∘ₗ eW.toLinearMap)
        ((T - LinearMap.id : W →ₗ[K] W) u) := by
  set φ : W →ₗ[F] (ι → F) := (LinearMap.range (Matrix.toLin' e)).subtype ∘ₗ eW.toLinearMap
  have hTφ : x *ᵥ φ u = φ (T u) := hT u
  calc
    Matrix.toLin' (x - 1) (φ u) = (x - 1) *ᵥ φ u := Matrix.toLin'_apply _ _
    _ = x *ᵥ φ u - φ u := by rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    _ = φ (T u) - φ u := by rw [hTφ]
    _ = φ ((T - LinearMap.id : W →ₗ[K] W) u) := by
      rw [LinearMap.sub_apply, LinearMap.id_apply, map_sub]

private lemma rckRPbt_range {ι F K W : Type} [Fintype ι] [DecidableEq ι] [Field F]
    [Field K] [Algebra F K] [AddCommGroup W] [Module F W] [Module K W] [IsScalarTower F K W]
    {e : Matrix ι ι F} (eW : W ≃ₗ[F] LinearMap.range (Matrix.toLin' e)) {x : Matrix ι ι F}
    {T : W →ₗ[K] W} (hT : ∀ w, x *ᵥ (eW w : ι → F) = (eW (T w) : ι → F)) :
    LinearMap.range (Matrix.toLin' ((x - 1) * e)) =
      ((LinearMap.range (T - LinearMap.id)).restrictScalars F).map
        ((LinearMap.range (Matrix.toLin' e)).subtype ∘ₗ eW.toLinearMap) := by
  let φ : W →ₗ[F] (ι → F) :=
    (LinearMap.range (Matrix.toLin' e)).subtype ∘ₗ eW.toLinearMap
  let S : W →ₗ[K] W := T - LinearMap.id
  have hφ_apply : ∀ w : W, φ w = (eW w : ι → F) := fun _ => rfl
  have hstep : ∀ (a : ι → F) (u : W), Matrix.toLin' e a = φ u →
      Matrix.toLin' ((x - 1) * e) a = φ (S u) := by
    intro a u ha
    rw [Matrix.toLin'_mul_apply, ha]
    exact rckRPbt_fix eW hT u
  change LinearMap.range (Matrix.toLin' ((x - 1) * e)) =
      ((LinearMap.range S).restrictScalars F).map φ
  ext v
  constructor
  · intro hv
    rw [LinearMap.mem_range] at hv
    obtain ⟨a, rfl⟩ := hv
    let u : W := eW.symm ⟨Matrix.toLin' e a, ⟨a, rfl⟩⟩
    have hu : φ u = Matrix.toLin' e a := by
      rw [hφ_apply u]
      simp [u]
    refine Submodule.mem_map.mpr ⟨S u, ?_, ?_⟩
    · rw [Submodule.restrictScalars_mem]
      exact LinearMap.mem_range.mpr ⟨u, rfl⟩
    · exact (hstep a u hu.symm).symm
  · intro hv
    rw [Submodule.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    rw [LinearMap.mem_range]
    have hw' : w ∈ LinearMap.range S :=
      (Submodule.restrictScalars_mem F _ w).mp hw
    obtain ⟨u, hu⟩ := hw'
    obtain ⟨a, ha⟩ := (eW u).2
    refine ⟨a, ?_⟩
    rw [← hu]
    exact hstep a u (by rw [ha, hφ_apply u])

private lemma rckRPbt_ker {ι F K W : Type} [Fintype ι] [DecidableEq ι] [Field F]
    [Field K] [Algebra F K] [AddCommGroup W] [Module F W] [Module K W] [IsScalarTower F K W]
    {e : Matrix ι ι F} (eW : W ≃ₗ[F] LinearMap.range (Matrix.toLin' e)) {x : Matrix ι ι F}
    {T : W →ₗ[K] W} (hT : ∀ w, x *ᵥ (eW w : ι → F) = (eW (T w) : ι → F)) :
    LinearMap.ker (Matrix.toLin' (x - 1)) ⊓ LinearMap.range (Matrix.toLin' e) =
      ((LinearMap.ker (T - LinearMap.id)).restrictScalars F).map
        ((LinearMap.range (Matrix.toLin' e)).subtype ∘ₗ eW.toLinearMap) := by
  let φ : W →ₗ[F] (ι → F) :=
    (LinearMap.range (Matrix.toLin' e)).subtype ∘ₗ eW.toLinearMap
  let S : W →ₗ[K] W := T - LinearMap.id
  have hφ_apply : ∀ w : W, φ w = (eW w : ι → F) := fun _ => rfl
  have hφ_inj : Function.Injective φ := by
    intro a b hab
    apply eW.injective
    apply Subtype.ext
    simpa [hφ_apply] using hab
  have hfix : ∀ u : W, Matrix.toLin' (x - 1) (φ u) = φ (S u) := rckRPbt_fix eW hT
  change LinearMap.ker (Matrix.toLin' (x - 1)) ⊓ LinearMap.range (Matrix.toLin' e) =
      ((LinearMap.ker S).restrictScalars F).map φ
  ext v
  constructor
  · intro hv
    rw [Submodule.mem_inf] at hv
    obtain ⟨hvker, hvr⟩ := hv
    rw [LinearMap.mem_ker] at hvker
    let w : W := eW.symm ⟨v, hvr⟩
    have hw : φ w = v := by
      rw [hφ_apply w]
      simp [w]
    refine Submodule.mem_map.mpr ⟨w, ?_, hw⟩
    rw [Submodule.restrictScalars_mem, LinearMap.mem_ker]
    have hzero : φ (S w) = 0 := by
      have h := hfix w
      rw [hw] at h
      rw [← h, hvker]
    exact hφ_inj (by rw [hzero, map_zero])
  · intro hv
    rw [Submodule.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    rw [Submodule.mem_inf]
    constructor
    · rw [LinearMap.mem_ker]
      rw [Submodule.restrictScalars_mem, LinearMap.mem_ker] at hw
      rw [hfix w, hw, map_zero]
    · rw [hφ_apply w]
      exact (eW w).2

theorem range_ker_block_of_action {ι F K W : Type} [Fintype ι] [DecidableEq ι] [Field F]
    [Field K] [Algebra F K] [AddCommGroup W] [Module F W] [Module K W] [IsScalarTower F K W]
    {e : Matrix ι ι F} (eW : W ≃ₗ[F] LinearMap.range (Matrix.toLin' e)) {x : Matrix ι ι F}
    {T : W →ₗ[K] W} (hT : ∀ w, x *ᵥ (eW w : ι → F) = (eW (T w) : ι → F)) :
    LinearMap.range (Matrix.toLin' ((x - 1) * e)) =
        ((LinearMap.range (T - LinearMap.id)).restrictScalars F).map
          ((LinearMap.range (Matrix.toLin' e)).subtype ∘ₗ eW.toLinearMap) ∧
      LinearMap.ker (Matrix.toLin' (x - 1)) ⊓ LinearMap.range (Matrix.toLin' e) =
        ((LinearMap.ker (T - LinearMap.id)).restrictScalars F).map
          ((LinearMap.range (Matrix.toLin' e)).subtype ∘ₗ eW.toLinearMap) :=
  ⟨rckRPbt_range eW hT, rckRPbt_ker eW hT⟩

end CFSG.StandardType.RCKRP
