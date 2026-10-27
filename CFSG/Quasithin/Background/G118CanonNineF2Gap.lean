module

public import CFSG.Quasithin.Background.E11Stmt

public section

namespace CFSG.Quasithin

namespace G11

namespace Canon

open scoped TensorProduct

@[expose] def permActCore (n : ℕ) (σ : Equiv.Perm (Fin n)) (x : ↥(CFSG.Quasithin.permCore n)) :
    ↥(CFSG.Quasithin.permCore n) :=
  ⟨fun i => (x : Fin n → ZMod 2) (σ⁻¹ i), by
    have hx : ∑ i, (x : Fin n → ZMod 2) i = 0 := x.2
    show ∑ i, (x : Fin n → ZMod 2) (σ⁻¹ i) = 0
    rw [Equiv.sum_comp σ⁻¹ (fun i => (x : Fin n → ZMod 2) i)]
    exact hx⟩

@[expose] def F2TensorGap : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (H : Subgroup (GLV V)) (I : Submodule (ZMod 2) V) (hHI : Invariant H I) (D : E11Data H I)
    (C Dg : Subgroup (GLV V)) (e : ↥C ≃* Equiv.Perm (Fin 3))
    (φ : ↥H ≃* ↥(alternatingGroup (Fin 5))) (σ : ↥Dg → Equiv.Perm (Fin 5)),
    Module.finrank (ZMod 2) V = 8 → Module.finrank D.F D.U = 2 → Nat.card D.F = 2 →
    (∀ c ∈ C, ∀ h ∈ H, h * c = c * h) →
    (∀ d ∈ Dg, ∀ c ∈ C, c * d = d * c) →
    (∀ d ∈ Dg, ∀ h ∈ H, d * h * d⁻¹ ∈ H) →
    (∀ (d : ↥Dg) (h g : ↥H), (g : GLV V) = (d : GLV V) * (h : GLV V) * (d : GLV V)⁻¹ →
        ((φ g : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) =
          σ d * ((φ h : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) * (σ d)⁻¹) →
    IsA5Module H I →
    ∃ ψ : V ≃ₗ[ZMod 2] (↥(CFSG.Quasithin.permCore 3) ⊗[ZMod 2] ↥(CFSG.Quasithin.permCore 5)),
      (∀ (c : ↥C) (x : ↥(CFSG.Quasithin.permCore 3)) (a : ↥(CFSG.Quasithin.permCore 5)),
        ψ ((c : GLV V) (ψ.symm (x ⊗ₜ a))) = permActCore 3 (e c) x ⊗ₜ a) ∧
      (∀ (d : ↥Dg) (x : ↥(CFSG.Quasithin.permCore 3)) (a : ↥(CFSG.Quasithin.permCore 5)),
        ψ ((d : GLV V) (ψ.symm (x ⊗ₜ a))) = x ⊗ₜ permActCore 5 (σ d) a)

end Canon

end G11

end CFSG.Quasithin
