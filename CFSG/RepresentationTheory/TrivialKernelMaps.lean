module

public import Mathlib.RepresentationTheory.Basic

public section

namespace CFSG.RepresentationTheory

open scoped TensorProduct

theorem linearMap_eq_zero_of_invariant
    {k B U V : Type*} [Field k] [Group B]
    [AddCommGroup U] [Module k U]
    [AddCommGroup V] [Module k V]
    (ρU : Representation k B U)
    (hU : ∀ ψ : U →ₗ[k] k,
      (∀ g u, ψ (ρU g u) = ψ u) → ψ = 0)
    (f : U →ₗ[k] V)
    (hf : ∀ g u, f (ρU g u) = f u) :
    f = 0 := by
  ext u
  refine (Module.forall_dual_apply_eq_zero_iff k (f u)).mp ?_
  intro φ
  have hφ : φ.comp f = 0 :=
    hU (φ.comp f) fun g u => by simp only [LinearMap.comp_apply, hf g u]
  have h := congrArg (fun l : U →ₗ[k] k => l u) hφ
  simpa using h

theorem equivariant_eq_of_comp_eq_of_fixed_kernel
    {k B U W P : Type*} [Field k] [Group B]
    [AddCommGroup U] [Module k U]
    [AddCommGroup W] [Module k W]
    [AddCommGroup P] [Module k P]
    (ρU : Representation k B U)
    (ρW : Representation k B W)
    (q : W →ₗ[k] P)
    (hfix : ∀ g w, q w = 0 → ρW g w = w)
    (hU : ∀ ψ : U →ₗ[k] k,
      (∀ g u, ψ (ρU g u) = ψ u) → ψ = 0)
    {f f' : U →ₗ[k] W}
    (hf : ∀ g u, f (ρU g u) = ρW g (f u))
    (hf' : ∀ g u, f' (ρU g u) = ρW g (f' u))
    (hq : q.comp f = q.comp f') :
    f = f' := by
  have hinv : ∀ g u, (f - f') (ρU g u) = (f - f') u := by
    intro g u
    have hq0 : q ((f - f') u) = 0 := by
      have hqu : q (f u) = q (f' u) := congrArg (fun l : U →ₗ[k] P => l u) hq
      rw [LinearMap.sub_apply, map_sub, hqu, sub_self]
    have heq : (f - f') (ρU g u) = ρW g ((f - f') u) := by
      rw [LinearMap.sub_apply, LinearMap.sub_apply, map_sub, hf g u, hf' g u]
    rw [heq, hfix g ((f - f') u) hq0]
  exact sub_eq_zero.mp (linearMap_eq_zero_of_invariant ρU hU (f - f') hinv)

theorem noInvariantFunctional_tprod_trivial
    {k B E X : Type*} [Field k] [Group B]
    [AddCommGroup E] [Module k E]
    [AddCommGroup X] [Module k X]
    (ρE : Representation k B E)
    (hE : ∀ ψ : E →ₗ[k] k,
      (∀ g e, ψ (ρE g e) = ψ e) → ψ = 0) :
    ∀ ψ : E ⊗[k] X →ₗ[k] k,
      (∀ g u,
        ψ ((ρE.tprod (Representation.trivial k B X)) g u) = ψ u) →
      ψ = 0 := by
  intro ψ hψ
  refine TensorProduct.ext' fun e x => ?_
  let φ : E →ₗ[k] k :=
    { toFun := fun e' => ψ (e' ⊗ₜ[k] x)
      map_add' := by
        intro e₁ e₂
        rw [TensorProduct.add_tmul, map_add]
      map_smul' := by
        intro a e'
        rw [← TensorProduct.smul_tmul', map_smul]
        rfl }
  have hφ : φ = 0 := by
    apply hE φ
    intro g e'
    have h := hψ g (e' ⊗ₜ[k] x)
    simpa [φ, Representation.tprod_apply] using h
  have hzero : φ e = 0 := by
    have := congrArg (fun l : E →ₗ[k] k => l e) hφ
    simpa using this
  simpa [φ] using hzero

end CFSG.RepresentationTheory

end
