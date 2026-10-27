module

public import Mathlib.LinearAlgebra.SpecialLinearGroup
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesAlt
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.Quasithin.H13.NQSetup

open CFSG.QuasithinUnique.Setup.SL2Modules

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

@[expose] def ExplicitNaturalFour (S : Subgroup (E ≃ₗ[ZMod 2] E)) : Prop :=
  ∃ (k : Type) (_ : Field k) (_ : Fintype k), Fintype.card k = 4 ∧
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module k V), Module.finrank k V = 2 ∧
      ∃ (β : S ≃* SpecialLinearGroup k V) (φ : E →+ V), Function.Surjective φ ∧
        (∀ (s : S) (e : E), φ ((s : E ≃ₗ[ZMod 2] E) e) = β s (φ e)) ∧
        ∀ s ∈ S, ∀ e : E, φ e = 0 → s e = e

@[expose] def ExplicitDeletedFive (S : Subgroup (E ≃ₗ[ZMod 2] E)) : Prop :=
  ∃ (Ω : Type) (_ : Fintype Ω) (_ : DecidableEq Ω), Fintype.card Ω = 5 ∧
    ∃ (β : S ≃* alternatingGroup Ω) (ψ : E ≃ₗ[ZMod 2] evenWeight Ω),
      ∀ (s : S) (e : E), (ψ ((s : E ≃ₗ[ZMod 2] E) e) : Ω → ZMod 2) =
        permAct (β s : Equiv.Perm Ω) (ψ e)

@[expose] def ExplicitNaturalThreeDouble (S : Subgroup (E ≃ₗ[ZMod 2] E)) : Prop :=
  ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 2) V), Module.finrank (ZMod 2) V = 3 ∧
    ∃ (β : S ≃* (V ≃ₗ[ZMod 2] V)) (ψ : E ≃ₗ[ZMod 2] V × V),
      ∀ (s : S) (e : E), ψ ((s : E ≃ₗ[ZMod 2] E) e) = (β s (ψ e).1, β s (ψ e).2)

@[expose] def ExplicitNaturalThreeExtension (S : Subgroup (E ≃ₗ[ZMod 2] E)) : Prop :=
  ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 2) V), Module.finrank (ZMod 2) V = 3 ∧
    ∃ (β : S ≃* (V ≃ₗ[ZMod 2] V)) (φ : E →ₗ[ZMod 2] V), Function.Surjective φ ∧
      (∀ (s : S) (e : E), φ ((s : E ≃ₗ[ZMod 2] E) e) = β s (φ e)) ∧
      ∀ s ∈ S, ∀ e : E, φ e = 0 → s e = e

end CFSG.Quasithin.H13.NQSetup
