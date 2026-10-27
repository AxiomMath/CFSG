module

public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.Quasithin.H13

@[expose] def Sp4PlaneFixFact : Prop :=
  ∀ (F : Type) [Field F] [Fintype F], Fintype.card F = 4 →
    ∀ (X : Subgroup ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F))
      (W : Submodule F (Fin 2 ⊕ Fin 2 → F)), 2 ≤ Module.finrank F W →
      (∀ g ∈ X, ∀ w ∈ W,
        (((g : ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F)) : GL (Fin 2 ⊕ Fin 2) F) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).mulVec w = w) →
      Nat.card X ≤ 64

end CFSG.Quasithin.H13
