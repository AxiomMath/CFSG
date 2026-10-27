module

public import CFSG.LocalAnalysis.StandardType.GGFrameModelStep
public import CFSG.LocalAnalysis.StandardType.GGCoxReflConv
public import Mathlib.LinearAlgebra.Matrix.ToLin

public section

namespace CFSG.StandardType.FrameRoute

open CFSG CFSG.Assembly

variable {G : Type} [Group G] {Bs : Subgroup G} {n : ℕ}

@[expose] noncomputable def frameLin (ψ : Additive ↥Bs ≃+ FEVec n) (φ : MulAut ↥Bs) :
    FEVec n →ₗ[ZMod 3] FEVec n where
  toFun v := ψ (Additive.ofMul (φ (Additive.toMul (ψ.symm v))))
  map_add' u v := by simp
  map_smul' c v := by
    let f : FEVec n →+ FEVec n :=
      (ψ.toAddMonoidHom.comp (MulEquiv.toAdditive φ).toAddMonoidHom).comp ψ.symm.toAddMonoidHom
    have hf : ∀ w, f w = ψ (Additive.ofMul (φ (Additive.toMul (ψ.symm w)))) := fun _ => rfl
    rw [RingHom.id_apply, ← hf, ← hf, ← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul,
      Nat.cast_smul_eq_nsmul, map_nsmul]

theorem frameLin_one (ψ : Additive ↥Bs ≃+ FEVec n) : frameLin ψ 1 = 1 := by
  apply LinearMap.ext
  intro v
  simp [frameLin]

theorem frameLin_mul (ψ : Additive ↥Bs ≃+ FEVec n) (φ₁ φ₂ : MulAut ↥Bs) :
    frameLin ψ (φ₁ * φ₂) = frameLin ψ φ₁ * frameLin ψ φ₂ := by
  apply LinearMap.ext
  intro v
  simp [frameLin]

@[expose] noncomputable def frameRho (ψ : Additive ↥Bs ≃+ FEVec n) : MulAut ↥Bs →* FEMat n where
  toFun φ := LinearMap.toMatrix' (frameLin ψ φ)
  map_one' := by rw [frameLin_one, LinearMap.toMatrix'_one]
  map_mul' φ₁ φ₂ := by rw [frameLin_mul, LinearMap.toMatrix'_mul]

theorem frameRho_mulVec (ψ : Additive ↥Bs ≃+ FEVec n) (φ : MulAut ↥Bs) (b : ↥Bs) :
    (frameRho ψ φ).mulVec (ψ (Additive.ofMul b)) = ψ (Additive.ofMul (φ b)) := by
  simp [frameRho, frameLin, LinearMap.toMatrix'_mulVec]

theorem frameRho_injective (ψ : Additive ↥Bs ≃+ FEVec n) : Function.Injective (frameRho ψ) := by
  intro φ₁ φ₂ h
  refine MulEquiv.ext fun b => ?_
  have := congrArg (fun m => m.mulVec (ψ (Additive.ofMul b))) h
  simp only [frameRho_mulVec] at this
  exact Additive.ofMul.injective (ψ.injective this)

theorem frameRho_eq_of_mulVec (ψ : Additive ↥Bs ≃+ FEVec n) {φ : MulAut ↥Bs} {m : FEMat n}
    (h : ∀ b : ↥Bs, m.mulVec (ψ (Additive.ofMul b)) = ψ (Additive.ofMul (φ b))) :
    frameRho ψ φ = m := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  obtain ⟨b, rfl⟩ : ∃ b : ↥Bs, ψ (Additive.ofMul b) = v :=
    ⟨Additive.toMul (ψ.symm v), by simp⟩
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, frameRho_mulVec, h]

theorem frameRho_mem_feT_of_isReflection [Finite G] (hBs : IsElemAbelian 3 Bs)
    {𝒜 : Subgroup (MulAut ↥Bs)} {M : CoxeterMatrix (Fin n)} {e : M.Group ≃* ↥𝒜}
    (hpres : GGCoxeterPres 3 𝒜 M e) (h3 : ∀ i j : Fin n, i ≠ j → M.M i j ≤ 3)
    (hnt : ∀ φ ∈ 𝒜, ¬ GGIsTransvection 3 φ) {ψ : Additive ↥Bs ≃+ FEVec n}
    {ρ : ↥𝒜 →* FEMat n}
    (hact : ∀ (φ : ↥𝒜) (b : ↥Bs), (ρ φ).mulVec (ψ (Additive.ofMul b)) =
      ψ (Additive.ofMul ((φ : MulAut ↥Bs) b)))
    (hρ : ∀ i, ρ (e (M.simple i)) = feS n i) {φ : MulAut ↥Bs} (hφ : φ ∈ 𝒜)
    (hr : GGIsReflection 3 φ) : frameRho ψ φ ∈ feT n := by
  have h := frameModel_coxRefl e hρ (φ := ⟨φ, hφ⟩)
    (ggCoxRefl_of_isReflection Nat.prime_three (by norm_num) hBs hpres h3 hnt hφ hr)
  rwa [← frameRho_eq_of_mulVec ψ (hact ⟨φ, hφ⟩)] at h

theorem exists_isReflection_frameRho_eq [Finite G] {𝒜 : Subgroup (MulAut ↥Bs)}
    {M : CoxeterMatrix (Fin n)} {e : M.Group ≃* ↥𝒜}
    (he : ∀ i, GGIsReflection 3 ((e (M.simple i) : ↥𝒜) : MulAut ↥Bs))
    {ψ : Additive ↥Bs ≃+ FEVec n} {ρ : ↥𝒜 →* FEMat n}
    (hact : ∀ (φ : ↥𝒜) (b : ↥Bs), (ρ φ).mulVec (ψ (Additive.ofMul b)) =
      ψ (Additive.ofMul ((φ : MulAut ↥Bs) b)))
    (hρ : ∀ i, ρ (e (M.simple i)) = feS n i) {t : FEMat n} (ht : t ∈ feT n) :
    ∃ φ ∈ 𝒜, GGIsReflection 3 φ ∧ frameRho ψ φ = t := by
  obtain ⟨φ, hφ, rfl⟩ := frameModel_feT e hρ ht
  exact ⟨φ, φ.2, ggCoxRefl_isReflection he hφ, frameRho_eq_of_mulVec ψ (hact φ)⟩

end CFSG.StandardType.FrameRoute

end
