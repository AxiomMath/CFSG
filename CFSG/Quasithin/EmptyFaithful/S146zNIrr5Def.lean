module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.Quasithin

@[expose] def A6NoIrr5 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) → Nat.card V = 32 →
    ∀ L : Subgroup (MulAut V), Nonempty (L ≃* alternatingGroup (Fin 6)) →
      ¬ (∀ S : Subgroup V, (∀ l ∈ L, ∀ w ∈ S, l w ∈ S) → S = ⊥ ∨ S = ⊤)

end CFSG.Quasithin
