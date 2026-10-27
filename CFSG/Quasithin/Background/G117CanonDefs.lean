module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.G11Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace G11

namespace Canon

open scoped TensorProduct

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def onesCore6 : ↥(permCore 6) :=
  ⟨fun _ => 1, by show (∑ _i : Fin 6, (1 : ZMod 2)) = 0; decide⟩

@[expose] def TensorA6Z3WithMarking (E P : Subgroup (GLV V))
    (φ : ↥E ≃* ↥(alternatingGroup (Fin 6))) : Prop :=
  ∃ (θ : ↥P ≃* (GaloisField 2 2)ˣ)
    (β : (↥(permCore 6) ⊗[ZMod 2] GaloisField 2 2) →ₗ[ZMod 2] V),
    Function.Surjective β ∧
    (∀ t, β t = 0 ↔ ∃ b : GaloisField 2 2, t = onesCore6 ⊗ₜ b) ∧
    (∀ (e : ↥E) (a a' : ↥(permCore 6)) (b : GaloisField 2 2),
      (a' : Fin 6 → ZMod 2) = permAct ((φ e : ↥(alternatingGroup (Fin 6))) : Equiv.Perm (Fin 6))
        (a : Fin 6 → ZMod 2) → β (a' ⊗ₜ b) = (e : GLV V) (β (a ⊗ₜ b))) ∧
    (∀ (p : ↥P) (a : ↥(permCore 6)) (b : GaloisField 2 2),
      β (a ⊗ₜ (((θ p : (GaloisField 2 2)ˣ) : GaloisField 2 2) * b)) = (p : GLV V) (β (a ⊗ₜ b)))

@[expose] def IsG112Ten (Γ X : Subgroup (GLV V)) : Prop :=
  Module.finrank (ZMod 2) V = 8 ∧
    ∃ (E P : Subgroup (GLV V)) (x : GLV V),
      E = (genFittingLayer ↥Γ).map Γ.subtype ∧ P = (CFSG.pCore 3 ↥Γ).map Γ.subtype ∧
      Nat.card P = 3 ∧ E ⊓ P = ⊥ ∧ (∀ e ∈ E, ∀ p ∈ P, e * p = p * e) ∧
      (genFittingFStar ↥Γ).map Γ.subtype = E ⊔ P ∧
      x ∈ X ∧ x ∈ Γ ∧ Γ = (E ⊔ P) ⊔ Subgroup.zpowers x ∧ (∀ p ∈ P, x * p * x⁻¹ = p⁻¹) ∧
      (∃ (φ : ↥E ≃* ↥(alternatingGroup (Fin 6))) (τ : Equiv.Perm (Fin 6)),
        τ.IsSwap ∧ TensorA6Z3WithMarking E P φ ∧
        ∀ e e' : ↥E, x * (e : GLV V) * x⁻¹ = (e' : GLV V) →
          ((φ e' : ↥(alternatingGroup (Fin 6))) : Equiv.Perm (Fin 6)) =
            τ * ((φ e : ↥(alternatingGroup (Fin 6))) : Equiv.Perm (Fin 6)) * τ⁻¹)

end Canon

end G11

end CFSG.Quasithin
