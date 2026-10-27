module

public import CFSG.RankThree.GF2n.Parrott.Basic

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open
open scoped commutatorElement

@[expose] def IsParrottE {G : Type} [Group G] (z : G) (E : Subgroup G) : Prop :=
  E ≤ H z ∧ E ≤ ⁅H z, H z⁆ ⊔ J z ∧ centerIn (J z) ≤ E ∧ IsElemAbelian 2 E ∧
    Nat.card E = 2 ^ 10 ∧ Nat.card ↥(E ⊓ J z) = 2 ^ 6 ∧
    E = H z ⊓ Subgroup.centralizer ((E ⊓ J z : Subgroup G) : Set G) ∧
    E.relIndex (Subgroup.normalizer (E : Set G) ⊓ H z) = 1920

end CFSG.RankThree.GF2n.Parrott
