module

public import CFSG.Quasithin.Background.G11Defs

public section

namespace CFSG.Quasithin

open CFSG.Quasithin.G11

@[expose] def B49Stmt : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (H : Subgroup (GLV V)) (U : Submodule (ZMod 2) V),
    (∀ v, B v v = 0) → (∀ v, (∀ w, B v w = 0) → v = 0) →
    (∀ h ∈ H, ∀ v w, B (h v) (h w) = B v w) →
    3 ≤ Module.finrank (ZMod 2) U → Isotropic B U →
    2 * Module.finrank (ZMod 2) U = Module.finrank (ZMod 2) V →
    Invariant H U → FaithfulOn H U → AutAll H U →
    (∃ E : Subgroup (GLV V), E ≤ H ∧ Nat.card E = 4 ∧
      (∃ a ∈ U, a ≠ 0 ∧ ∀ e ∈ E, ∀ u ∈ U, e u - u ∈ Submodule.span (ZMod 2) {a}) ∧
      (∀ e ∈ E, ∀ e' ∈ E, ∀ v : V, e (e' v - v) = e' v - v)) →
    ∃ U' : Submodule (ZMod 2) V, Invariant H U' ∧ IsCompl U U'

end CFSG.Quasithin
