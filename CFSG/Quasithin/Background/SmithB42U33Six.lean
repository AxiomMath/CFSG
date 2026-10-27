module

public import CFSG.Quasithin.Background.SmithB42Families

public section

namespace CFSG.Quasithin

@[expose] def U33SixNatural : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) → Nat.card V = 2 ^ 6 →
    ∀ L : Subgroup (MulAut V), B42TypeU33 ↥L → G2NaturalDerived L ⊤ ⊥ 1

end CFSG.Quasithin
