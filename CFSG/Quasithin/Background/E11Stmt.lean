module

public import CFSG.Quasithin.Background.G11Basic

public section

namespace CFSG.Quasithin

namespace G11

open scoped LinearAlgebra.Projectivization

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def endOn (H : Subgroup (GLV V)) (I : Submodule (ZMod 2) V) :
    Subalgebra (ZMod 2) (Module.End (ZMod 2) I) :=
  Subalgebra.centralizer (ZMod 2)
    {f | ∃ (h : GLV V) (hh : conjSub h I = I), h ∈ H ∧
      f = ((restrictEquiv h I hh : I ≃ₗ[ZMod 2] I) : I →ₗ[ZMod 2] I)}

@[expose] def ActsOnPoints {F U : Type} [Field F] [AddCommGroup U] [Module F U]
    {H : Subgroup (GLV V)} (ψ : {J : Submodule (ZMod 2) V // IrrPlus H J} ≃ ℙ F U)
    (g : GLV V) (π : ℙ F U → ℙ F U) : Prop :=
  ∀ (J : Submodule (ZMod 2) V) (hJ : IrrPlus H J), ∃ hJ' : IrrPlus H (conjSub g J),
    ψ ⟨conjSub g J, hJ'⟩ = π (ψ ⟨J, hJ⟩)

structure E11Data {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (H : Subgroup (GLV V))
    (I : Submodule (ZMod 2) V) : Type 1 where
  F : Type
  [instField : Field F]
  [instAlgebra : Algebra (ZMod 2) F]
  [instFiniteF : Finite F]
  [instCharP : CharP F 2]
  U : Type
  [instAddCommGroup : AddCommGroup U]
  [instModule : Module F U]
  [instFiniteU : Finite U]
  [instModuleFinite : Module.Finite F U]
  ψ : {J : Submodule (ZMod 2) V // IrrPlus H J} ≃ ℙ F U
  endEquiv : endOn H I ≃ₐ[ZMod 2] F
  finrank_mul :
    Module.finrank F U * Module.finrank (ZMod 2) I = Module.finrank (ZMod 2) V
  θ : Subgroup.centralizer (H : Set (GLV V)) ≃* (U ≃ₗ[F] U)
  θ_acts : ∀ c : Subgroup.centralizer (H : Set (GLV V)), ActsOnPoints ψ (c : GLV V) (θ c • ·)
  semilinear : ∀ g ∈ Subgroup.normalizer (H : Set (GLV V)),
    ∃ (τ : F ≃+* F) (σ : U →ₛₗ[(τ : F →+* F)] U) (hσ : Function.Bijective σ),
      ActsOnPoints ψ g (Projectivization.map σ hσ.1) ∧
      ∀ c c' : Subgroup.centralizer (H : Set (GLV V)),
        (c' : GLV V) * g = g * c → ∀ u : U, θ c' (σ u) = σ (θ c u)
  exists_subspace : ∀ M : Submodule (ZMod 2) V, Invariant H M →
    ∃ S : Submodule F U,
      (∀ (J : Submodule (ZMod 2) V) (hJ : IrrPlus H J), J ≤ M ↔ (ψ ⟨J, hJ⟩).submodule ≤ S) ∧
      Module.finrank F S * Module.finrank (ZMod 2) I = Module.finrank (ZMod 2) M
  κ : F →ₐ[ZMod 2] Module.End (ZMod 2) V
  κ_injective : Function.Injective κ
  κ_comm : ∀ (f : F) (h : GLV V), h ∈ H →
    κ f * (h : Module.End (ZMod 2) V) = (h : Module.End (ZMod 2) V) * κ f
  κ_stable : ∀ (f : F) (J : Submodule (ZMod 2) V), IrrPlus H J → ∀ v ∈ J, κ f v ∈ J
  κ_apply : ∀ (f : endOn H I) (i : I),
    κ (endEquiv f) (i : V) = (((f : Module.End (ZMod 2) I) i : I) : V)
  κ_conj : ∀ g ∈ Subgroup.normalizer (H : Set (GLV V)), ∀ (τ : F ≃+* F)
    (σ : U →ₛₗ[(τ : F →+* F)] U), Function.Bijective σ →
      (∀ c c' : Subgroup.centralizer (H : Set (GLV V)),
        (c' : GLV V) * g = g * c → ∀ u : U, θ c' (σ u) = σ (θ c u)) →
      ∀ f : F, (g : Module.End (ZMod 2) V) * κ f = κ (τ f) * (g : Module.End (ZMod 2) V)

attribute [instance] E11Data.instField E11Data.instAlgebra E11Data.instFiniteF
  E11Data.instCharP E11Data.instAddCommGroup E11Data.instModule E11Data.instFiniteU
  E11Data.instModuleFinite

@[expose] def E11Stmt : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (H : Subgroup (GLV V))
    (I : Submodule (ZMod 2) V), Homogeneous H → IrrPlus H I → fixedSpace H = ⊥ →
    sSup {J : Submodule (ZMod 2) V | IsIrr H J} = ⊤ → Nonempty (E11Data H I)

end G11

end CFSG.Quasithin
