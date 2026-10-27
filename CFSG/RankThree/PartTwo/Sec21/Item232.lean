module

public import CFSG.RankThree.PartTwo.Sec21.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type} [Group G]

@[expose] def Item232Concl (A : Subgroup G) : Prop :=
  A ≤ iGroup A ∧ ∀ P : Sylow 3 (iGroup A), A ≤ (P : Subgroup (iGroup A)).map (iGroup A).subtype →
    (Nonempty ((P : Subgroup (iGroup A)) ≃*
        Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3)) ∨
      Nonempty ((P : Subgroup (iGroup A)) ≃*
        (Multiplicative (ZMod 9) × Multiplicative (ZMod 9) ≀ᵣ Multiplicative (ZMod 3)))) ∧
    (CFSG.elemThompson ((P : Subgroup (iGroup A)).map (iGroup A).subtype) 3).map
        ((P : Subgroup (iGroup A)).map (iGroup A).subtype).subtype = A ∧
    Subgroup.normalizer (A : Set G) ≤ nGroup A ∧
    ∃ S : Sylow 3 G, (S : Subgroup G) = (P : Subgroup (iGroup A)).map (iGroup A).subtype

@[expose] def Item232 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Item232Concl A

end CFSG.RankThree.PartTwo.Sec21
