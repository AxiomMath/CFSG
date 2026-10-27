module

public import CFSG.Open.StatedDefs
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Open

@[expose] def GriessSL34Statement : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 4 →
  ∀ (E : Type) [Group E] [Finite E] (Y : Subgroup E), Y ≤ Subgroup.center E →
    commutator E = ⊤ →
  ∀ π : E →* GL (Fin 3) K, π.range = StatedSL 3 K → π.ker = Y →
    Y = ⊥ ∨ ∀ A : Subgroup E, A ⊓ Y = ⊥ → IsElemAbelian 2 A →
      (∀ e ∈ Subgroup.normalizer ((A ⊔ Y : Subgroup E) : Set E),
        e ∈ Subgroup.normalizer (A : Set E)) →
      Nat.card A < 16

end CFSG.RankThree.GF2n.Stroth80
