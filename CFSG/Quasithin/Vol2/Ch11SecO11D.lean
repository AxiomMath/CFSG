module

public import CFSG.Quasithin.Vol2.Ch11SecSFacts4

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint

@[expose] def FactU35UniqueL24 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], (IsSU3 5 Q ∨ IsPSU 3 5 1 Q) →
    ∀ S : Subgroup Q, QuasithinUnique.IsSylowTwoOf S ⊤ →
      ∀ B₁ B₂ : Subgroup Q, IsL24Sub S B₁ → IsL24Sub S B₂ → B₁ = B₂

end CFSG.Quasithin.Vol2.Ch11.SecS
