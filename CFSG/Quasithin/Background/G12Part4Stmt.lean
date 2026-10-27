module

public import CFSG.Quasithin.Background.G12Stmts

public section

namespace CFSG.Quasithin.G11

@[expose] def G1212Part4 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (H K Q : Subgroup (GLV V)) (W : Submodule (ZMod 2) V) (v : V)
    (f : LinearMap.BilinForm (ZMod 2) V),
    G1212Hyp H K Q W v → IsSymplectic f → K ⊔ Q ≤ spSub f → W = perp f v →
    G121Concl f (K ⊔ Q) v →
    (H ≤ spSub f ∨ ∃ ω : GLV V, (∀ x, ω (ω x) + ω x + x = 0) ∧
      H = Subgroup.normalizer (Subgroup.zpowers ω : Set (GLV V)))

end CFSG.Quasithin.G11
