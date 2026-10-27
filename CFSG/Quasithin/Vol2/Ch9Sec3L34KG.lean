module

public import CFSG.Quasithin.Background.Module
public import CFSG.Quasithin.Background.A1cModuleDefs
public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Quasithin

@[expose] def FactL34QuadThree : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ X : Subgroup (MulAut V), XMod.IsIrrSec ↥X (⊥ : Subgroup V) ⊤ →
      ∀ L : Subgroup (MulAut V), L ≤ X → X ≤ Subgroup.normalizer (L : Set (MulAut V)) →
      IsPSL 3 2 2 ↥L → (∀ x ∈ X, (∀ l ∈ L, x * l = l * x) → x = 1) →
      (∀ x ∈ X, ∃ m : ℕ, x ^ 2 ^ m ∈ L) →
      ∀ A : Subgroup (MulAut V), A ≤ X → A ≠ ⊥ → IsElemAbelian2 A → IsQuadratic A →
        Nat.card A ^ 3 * Nat.card (fixV A) ≤ Nat.card V

end CFSG.Quasithin.H13.Ch9
