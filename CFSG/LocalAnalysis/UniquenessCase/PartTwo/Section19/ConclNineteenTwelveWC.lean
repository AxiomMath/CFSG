module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G]

@[expose] def Concl19_12wc (A : Subgroup G) : Prop :=
  ∀ E : Subgroup G, E ≤ A → IsElemAbelian 3 E → Nat.card E = 9 →
    ∀ g : G, E.map (MulAut.conj g).toMonoidHom ≤ centralizer (E : Set G) →
      E.map (MulAut.conj g).toMonoidHom = E

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
