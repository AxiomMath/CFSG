module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.Defs

namespace CFSG
end CFSG
open CFSG

/-!
# Section 4, equation (11): finite pair-counting infrastructure

The source's final inequality counts pairs `(X,Y)` and injects them into the
conjugacy orbit of a fixed order-`p` subgroup.  This owner isolates the
cardinality step from the later PSL₂-specific construction of the pair map.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u v

/-- An injective pair map gives the expected product-cardinality bound. -/
public theorem Nat.card_mul_le_of_injective_pair
    {A : Type u} {B : Type v} {C : Type max u v}
    [Finite A] [Finite B] [Finite C]
    (f : A × B → C) (hf : Function.Injective f) :
    Nat.card A * Nat.card B ≤ Nat.card C := by
  have hcard : Nat.card (A × B) ≤ Nat.card C :=
    Nat.card_le_card_of_injective f hf
  simpa [Nat.card_prod] using hcard

end CFSG.GorensteinWalter
