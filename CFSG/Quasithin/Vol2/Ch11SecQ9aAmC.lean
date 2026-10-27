module

public import CFSG.Quasithin.Vol2.Ch11SecSFacts4

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open

@[expose] def FactParabRadical : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], Shape4 Q →
    ∀ S B : Subgroup Q, QuasithinUnique.IsSylowTwoOf S ⊤ → IsL24Sub S B →
      ⁅pCoreOf 2 B, B⁆ ≠ ⊥

end CFSG.Quasithin.Vol2.Ch11.SecS
