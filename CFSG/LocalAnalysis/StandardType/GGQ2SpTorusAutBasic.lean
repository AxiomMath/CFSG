module

public import CFSG.LocalAnalysis.StandardType.GGQ2SpNormalizerStatements

public section

namespace CFSG.StandardType.GGQ2Frame.SpBlocks

open Matrix
open CFSG.Open (StatedSp)

variable {K : Type} [Field K] (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (m : ℕ)

theorem one_mem_torusAut (X : Subgroup ↥(StatedSp m K)) :
    (1 : PlaneRaw.V m ≃ₗ[ZMod 3] PlaneRaw.V m) ∈ torusAut ζ m X :=
  ⟨1, X.one_mem, fun u => by rw [one_mul, inv_one, mul_one]; rfl⟩

theorem mul_mem_torusAut {X : Subgroup ↥(StatedSp m K)}
    {φ ψ : PlaneRaw.V m ≃ₗ[ZMod 3] PlaneRaw.V m} (hφ : φ ∈ torusAut ζ m X)
    (hψ : ψ ∈ torusAut ζ m X) : φ * ψ ∈ torusAut ζ m X := by
  obtain ⟨y, hy, hyφ⟩ := hφ
  obtain ⟨z, hz, hzψ⟩ := hψ
  refine ⟨y * z, X.mul_mem hy hz, fun u => ?_⟩
  rw [LinearEquiv.mul_apply, ← hyφ, ← hzψ]
  group

theorem inv_mem_torusAut {X : Subgroup ↥(StatedSp m K)}
    {φ : PlaneRaw.V m ≃ₗ[ZMod 3] PlaneRaw.V m} (hφ : φ ∈ torusAut ζ m X) :
    φ⁻¹ ∈ torusAut ζ m X := by
  obtain ⟨y, hy, hyφ⟩ := hφ
  refine ⟨y⁻¹, X.inv_mem hy, fun u => ?_⟩
  have h := hyφ (φ⁻¹ u)
  have hu : φ (φ⁻¹ u) = u := by rw [← LinearEquiv.mul_apply, mul_inv_cancel]; rfl
  rw [hu] at h
  rw [← h]
  group

theorem closure_subset_torusAut {X : Subgroup ↥(StatedSp m K)}
    {T : Set (PlaneRaw.V m ≃ₗ[ZMod 3] PlaneRaw.V m)} (hT : T ⊆ torusAut ζ m X) :
    ((Subgroup.closure T : Subgroup _) : Set _) ⊆ torusAut ζ m X := by
  intro φ (hφ : φ ∈ Subgroup.closure T)
  induction hφ using Subgroup.closure_induction with
  | mem x hx => exact hT hx
  | one => exact one_mem_torusAut ζ m X
  | mul x y _ _ hx hy => exact mul_mem_torusAut ζ m hx hy
  | inv x _ hx => exact inv_mem_torusAut ζ m hx

theorem torusAut_mono {X Y : Subgroup ↥(StatedSp m K)} (h : X ≤ Y) :
    torusAut ζ m X ⊆ torusAut ζ m Y :=
  fun _ ⟨y, hy, hyφ⟩ => ⟨y, h hy, hyφ⟩

end CFSG.StandardType.GGQ2Frame.SpBlocks
