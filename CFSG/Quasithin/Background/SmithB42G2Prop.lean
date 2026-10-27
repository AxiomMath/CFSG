module

public import CFSG.Quasithin.Background.A1cModuleDefs
public import CFSG.Quasithin.Background.B4ModelsLie
public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.Quasithin

open CFSG.Blueprint

@[expose] def GM04G2EvenFFNatural : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (L : Subgroup (MulAut W)) (f : ℕ), 2 ≤ f → Subgroup.center ↥L = ⊥ →
      ChevalleyExceptionalModel (↥L ⧸ Subgroup.center ↥L) .G2 2 f →
      XMod.IsIrrSec ↥L (⊥ : Subgroup W) ⊤ →
      ∀ E : Subgroup (MulAut W), E ≤ Subgroup.normalizer (L : Set (MulAut W)) → E ≠ ⊥ →
        IsElemAbelian2 E → Nat.card W ≤ Nat.card E * Nat.card (fixV E) →
        G2Natural L ⊤ ⊥ f

end CFSG.Quasithin
