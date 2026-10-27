module

public import CFSG.LocalAnalysis.StandardType.GGQ2LinNormalizerStatements
public import CFSG.LocalAnalysis.StandardType.GGQ2SpNormalizerStatements

public section

namespace CFSG.StandardType.GGQ2Frame.LinBlocks

open Matrix
open CFSG.Open (StatedSp)

variable {K : Type} [Field K] (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K)
  (t : ℕ) (ε : Fin 2)

theorem one_mem_torusAut (X : Subgroup (GL (LinIdx t ε) K)) :
    (1 : PlaneRaw.V t ≃ₗ[ZMod 3] PlaneRaw.V t) ∈ torusAut ζ t ε X :=
  ⟨1, X.one_mem, fun u => by rw [one_mul, inv_one, mul_one]; rfl⟩

theorem mul_mem_torusAut {X : Subgroup (GL (LinIdx t ε) K)}
    {φ ψ : PlaneRaw.V t ≃ₗ[ZMod 3] PlaneRaw.V t} (hφ : φ ∈ torusAut ζ t ε X)
    (hψ : ψ ∈ torusAut ζ t ε X) : φ * ψ ∈ torusAut ζ t ε X := by
  obtain ⟨y, hy, hyφ⟩ := hφ
  obtain ⟨z, hz, hzψ⟩ := hψ
  refine ⟨y * z, X.mul_mem hy hz, fun u => ?_⟩
  rw [LinearEquiv.mul_apply, ← hyφ, ← hzψ]
  group

theorem inv_mem_torusAut {X : Subgroup (GL (LinIdx t ε) K)}
    {φ : PlaneRaw.V t ≃ₗ[ZMod 3] PlaneRaw.V t} (hφ : φ ∈ torusAut ζ t ε X) :
    φ⁻¹ ∈ torusAut ζ t ε X := by
  obtain ⟨y, hy, hyφ⟩ := hφ
  refine ⟨y⁻¹, X.inv_mem hy, fun u => ?_⟩
  have h := hyφ (φ⁻¹ u)
  have hu : φ (φ⁻¹ u) = u := by rw [← LinearEquiv.mul_apply, mul_inv_cancel]; rfl
  rw [hu] at h
  rw [← h]
  group

theorem closure_subset_torusAut {X : Subgroup (GL (LinIdx t ε) K)}
    {T : Set (PlaneRaw.V t ≃ₗ[ZMod 3] PlaneRaw.V t)} (hT : T ⊆ torusAut ζ t ε X) :
    ((Subgroup.closure T : Subgroup _) : Set _) ⊆ torusAut ζ t ε X := by
  intro φ (hφ : φ ∈ Subgroup.closure T)
  induction hφ using Subgroup.closure_induction with
  | mem x hx => exact hT hx
  | one => exact one_mem_torusAut ζ t ε X
  | mul x y _ _ hx hy => exact mul_mem_torusAut ζ t ε hx hy
  | inv x _ hx => exact inv_mem_torusAut ζ t ε hx

theorem torusAut_mono {X Y : Subgroup (GL (LinIdx t ε) K)} (h : X ≤ Y) :
    torusAut ζ t ε X ⊆ torusAut ζ t ε Y :=
  fun _ ⟨y, hy, hyφ⟩ => ⟨y, h hy, hyφ⟩

theorem tau_eq_planeExt (u : PlaneRaw.V t) :
    tau ζ t ε u = planeExt t ε ((SpBlocks.tau ζ t u : ↥(StatedSp t K)) : GL (Fin t ⊕ Fin t) K) :=
  rfl

theorem mem_torusAut_of_mem_spTorusAut {X : Subgroup ↥(StatedSp t K)}
    {Y : Subgroup (GL (LinIdx t ε) K)}
    (hXY : ∀ x ∈ X, planeExt t ε ((x : ↥(StatedSp t K)) : GL (Fin t ⊕ Fin t) K) ∈ Y)
    {φ : PlaneRaw.V t ≃ₗ[ZMod 3] PlaneRaw.V t} (hφ : φ ∈ SpBlocks.torusAut ζ t X) :
    φ ∈ torusAut ζ t ε Y := by
  obtain ⟨y, hy, hyφ⟩ := hφ
  refine ⟨planeExt t ε ((y : ↥(StatedSp t K)) : GL (Fin t ⊕ Fin t) K), hXY y hy, fun u => ?_⟩
  rw [tau_eq_planeExt, tau_eq_planeExt, ← hyφ u]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]

@[expose] def LinTorusAutSubsetSignedPerm : Prop :=
  ∀ {K : Type} [Field K] [Finite K] [CharP K 2]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ) (ε : Fin 2),
    Nat.card K = 2 → Function.Injective ζ → ∀ X : Subgroup (GL (LinIdx t ε) K),
      torusAut ζ t ε X ⊆ ((PlaneRaw.signedPermGroup t : Subgroup _) : Set _)

end CFSG.StandardType.GGQ2Frame.LinBlocks
