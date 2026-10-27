module

public import CFSG.Quasithin.Background.G12Rad

public section

namespace CFSG.Quasithin.G11

@[expose] def G12FourFact : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v : V),
    IsSymplectic B → Module.finrank (ZMod 2) V = 4 → Γ ≤ spSub B → v ≠ 0 →
    (∀ w, w ≠ 0 → IsStarVec B Γ w) → radE B v 0 1 ∉ Γ → (∀ w, w ≠ 0 → ∃ g ∈ Γ, g v = w) →
    (Γ = ⁅spSub B, spSub B⁆ ∨
      (Nonempty (↥Γ ≃* Equiv.Perm (Fin 5)) ∧ ∃ A : Subgroup (GLV V), A ≤ Γ ∧ IsL24ModuleFor A))

@[expose] def G1212PartFourFact : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (H K Q : Subgroup (GLV V)) (W : Submodule (ZMod 2) V) (v : V)
    (f : LinearMap.BilinForm (ZMod 2) V),
    G1212Hyp H K Q W v → IsSymplectic f → K ⊔ Q ≤ spSub f → W = perp f v →
    G121Concl f (K ⊔ Q) v → Module.finrank (ZMod 2) V = 4 →
    (H ≤ spSub f ∨ ∃ ω : GLV V, (∀ x, ω (ω x) + ω x + x = 0) ∧
      H = Subgroup.normalizer (Subgroup.zpowers ω : Set (GLV V)))

end CFSG.Quasithin.G11
