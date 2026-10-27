module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.ZMod

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Module Submodule

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

private theorem pgl_beta_right_zero {U₁ U₂ : Submodule (ZMod 2) W} {β : W → W → ZMod 2}
    (hb2 : ∀ u ∈ U₁, ∀ v₁ ∈ U₂, ∀ v₂ ∈ U₂, β u (v₁ + v₂) = β u v₁ + β u v₂)
    {u : W} (hu : u ∈ U₁) : β u 0 = 0 := by
  have h : β u 0 = β u 0 + β u 0 := by
    simpa using hb2 u hu 0 (zero_mem U₂) 0 (zero_mem U₂)
  exact h.trans (CharTwo.add_self_eq_zero _)

private theorem pgl_beta_left_zero {U₁ U₂ : Submodule (ZMod 2) W} {β : W → W → ZMod 2}
    (hb1 : ∀ u₁ ∈ U₁, ∀ u₂ ∈ U₁, ∀ v ∈ U₂, β (u₁ + u₂) v = β u₁ v + β u₂ v)
    {v : W} (hv : v ∈ U₂) : β 0 v = 0 := by
  have h : β 0 v = β 0 v + β 0 v := by
    simpa using hb1 0 (zero_mem U₁) 0 (zero_mem U₁) v hv
  exact h.trans (CharTwo.add_self_eq_zero _)

variable [Finite W]

private theorem pgl_add_self_eq_zero (x : W) : x + x = 0 := by
  rw [← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 from by decide, zero_smul]

private theorem pgl_sum_single (x : Fin 3 → ZMod 2) :
    (∑ i, x i • Pi.single i (1 : ZMod 2)) = x := by
  conv_rhs => rw [← (Pi.basisFun (ZMod 2) (Fin 3)).sum_repr x]
  simp

theorem pgl_dual_equiv {U₁ U₂ : Submodule (ZMod 2) W}
    (φ₁ : ↥U₁ ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) (β : W → W → ZMod 2)
    (hb1 : ∀ u₁ ∈ U₁, ∀ u₂ ∈ U₁, ∀ v ∈ U₂, β (u₁ + u₂) v = β u₁ v + β u₂ v)
    (hb2 : ∀ u ∈ U₁, ∀ v₁ ∈ U₂, ∀ v₂ ∈ U₂, β u (v₁ + v₂) = β u v₁ + β u v₂)
    (hl : ∀ u ∈ U₁, (∀ v ∈ U₂, β u v = 0) → u = 0)
    (hr : ∀ v ∈ U₂, (∀ u ∈ U₁, β u v = 0) → v = 0) :
    ∃ φ₂ : ↥U₂ ≃ₗ[ZMod 2] (Fin 3 → ZMod 2),
      ∀ (x : Fin 3 → ZMod 2) (v : ↥U₂),
        β (φ₁.symm x) (v : W) = dotProduct x (φ₂ v) := by
  classical
  haveI : FiniteDimensional (ZMod 2) W := by
    haveI : FiniteDimensional (ZMod 2) (⊤ : Submodule (ZMod 2) W) := by
      rw [show (⊤ : Submodule (ZMod 2) W) = Submodule.span (ZMod 2) Set.univ from
        Submodule.span_univ.symm]
      exact Module.Finite.span_of_finite (ZMod 2) (A := Set.univ)
        (Set.toFinite (Set.univ : Set W))
    exact Module.Finite.equiv
      (Submodule.topEquiv : ↥(⊤ : Submodule (ZMod 2) W) ≃ₗ[ZMod 2] W)
  let b : Fin 3 → ↥U₁ := fun i => φ₁.symm (Pi.single i (1 : ZMod 2))
  let βu : ↥U₁ → ↥U₂ →ₗ[ZMod 2] ZMod 2 := fun u =>
    AddMonoidHom.toZModLinearMap 2
      { toFun := fun v => β (u : W) (v : W)
        map_zero' := pgl_beta_right_zero hb2 u.2
        map_add' := fun v w => hb2 u u.2 v v.2 w w.2 }
  let βL : ↥U₁ →ₗ[ZMod 2] Module.Dual (ZMod 2) ↥U₂ :=
    AddMonoidHom.toZModLinearMap 2
      { toFun := βu
        map_zero' := by
          ext v
          exact pgl_beta_left_zero hb1 v.2
        map_add' := fun u w => by
          ext v
          exact hb1 u u.2 w w.2 v v.2 }
  let ψ : ↥U₂ →ₗ[ZMod 2] (Fin 3 → ZMod 2) :=
    AddMonoidHom.toZModLinearMap 2
      { toFun := fun v => fun i => β (b i : W) (v : W)
        map_zero' := by
          funext i
          exact pgl_beta_right_zero hb2 (b i).2
        map_add' := fun v w => by
          funext i
          exact hb2 (b i) (b i).2 v v.2 w w.2 }
  have hβL_apply : ∀ (u : ↥U₁) (v : ↥U₂), βL u v = β (u : W) (v : W) := by
    intro u v
    simp [βL, βu]
  have hψ_apply : ∀ (v : ↥U₂) (i : Fin 3), ψ v i = β (b i : W) (v : W) := by
    intro v i
    simp [ψ, b]
  have hkeyψ : ∀ (x : Fin 3 → ZMod 2) (v : ↥U₂),
      β (φ₁.symm x) (v : W) = dotProduct x (ψ v) := by
    intro x v
    have hx : φ₁.symm x = ∑ i, x i • b i := by
      apply φ₁.injective
      simp only [map_sum, map_smul, LinearEquiv.apply_symm_apply, b]
      exact (pgl_sum_single x).symm
    rw [← hβL_apply (φ₁.symm x) v, hx, map_sum]
    simp only [map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, dotProduct,
      hψ_apply, hβL_apply]
  have hψ_inj : Function.Injective ψ := by
    intro v w hvw
    apply Subtype.ext
    have huv : ∀ u ∈ U₁, β u (v : W) = β u (w : W) := by
      intro u hu
      have hv' := hkeyψ (φ₁ ⟨u, hu⟩) v
      have hw' := hkeyψ (φ₁ ⟨u, hu⟩) w
      rw [LinearEquiv.symm_apply_apply] at hv' hw'
      rw [hv', hw', hvw]
    have hsum : (v : W) + (w : W) = 0 := by
      refine hr _ (add_mem v.2 w.2) (fun u hu => ?_)
      rw [hb2 u hu (v : W) v.2 (w : W) w.2, huv u hu, CharTwo.add_self_eq_zero]
    have h2 : (v : W) + (w : W) = (w : W) + (w : W) := by
      rw [hsum, pgl_add_self_eq_zero]
    exact add_right_cancel h2
  have hβL_inj : Function.Injective βL := by
    intro u w huw
    apply Subtype.ext
    have hsum : (u : W) + (w : W) = 0 := by
      refine hl _ (add_mem u.2 w.2) (fun v hv => ?_)
      have hv' : β (u : W) v = β (w : W) v := by
        rw [← hβL_apply u ⟨v, hv⟩, ← hβL_apply w ⟨v, hv⟩]
        exact DFunLike.congr_fun huw ⟨v, hv⟩
      rw [hb1 u u.2 w w.2 v hv, hv', CharTwo.add_self_eq_zero]
    have h2 : (u : W) + (w : W) = (w : W) + (w : W) := by
      rw [hsum, pgl_add_self_eq_zero]
    exact add_right_cancel h2
  have hfin_fun : finrank (ZMod 2) (Fin 3 → ZMod 2) = 3 := Module.finrank_fin_fun (ZMod 2)
  have hfinU₁ : finrank (ZMod 2) ↥U₁ = 3 := by
    rw [LinearEquiv.finrank_eq φ₁, hfin_fun]
  have hle₁ : finrank (ZMod 2) ↥U₁ ≤ finrank (ZMod 2) ↥U₂ := by
    have h := LinearMap.finrank_le_finrank_of_injective (f := βL) hβL_inj
    rwa [Subspace.dual_finrank_eq] at h
  have hle₂ : finrank (ZMod 2) ↥U₂ ≤ finrank (ZMod 2) (Fin 3 → ZMod 2) :=
    LinearMap.finrank_le_finrank_of_injective (f := ψ) hψ_inj
  have hfinU₂ : finrank (ZMod 2) ↥U₂ = 3 := by omega
  refine ⟨LinearMap.linearEquivOfInjective ψ hψ_inj (by rw [hfinU₂, hfin_fun]), ?_⟩
  intro x v
  rw [LinearMap.linearEquivOfInjective_apply]
  exact hkeyψ x v

end CFSG.LocalAnalysis.WeakClosure81

end
