module

public import CFSG.Quasithin.Background.Module
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.Quasithin

@[expose] def AsI231A6 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) → Nat.card W = 2 ^ 5 →
    ∀ L P : Subgroup (MulAut W), Nonempty (↥L ≃* ↥(alternatingGroup (Fin 6))) → commV L = ⊤ →
      IsPGroup 2 P → P ≤ Subgroup.normalizer (L : Set (MulAut W)) → ¬ fixV P ≤ fixV L

end CFSG.Quasithin
