module

public import CFSG.RankThree.PartTwo.Sec13.Notation
public import CFSG.RankThree.PartTwo.Sec4.LThreePiOn

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def Hyp138 {G : Type} [Group G] [Finite G] (A : Subgroup G) (c : G) (L E : Subgroup G) :
    Prop :=
  Sec13Data G A c L ∧ IsLThreePi (L ⧸ aschbacherSolvableCore 3 L) ∧ c ∈ E ∧
    CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 27 ∧
    E ≤ Subgroup.normalizer (L : Set G) ∧
    Late.sectionCentralizer E L ((aschbacherSolvableCore 3 L).map L.subtype) =
      (Subgroup.zpowers c : Set G) ∧
    (HypS E ∨ HypT E) ∧ Sec4.IsTypeCOn E L

@[expose] def IsF138 {G : Type} [Group G] (L E F : Subgroup G) : Prop :=
  F ≤ E ⊔ L ∧ CFSG.Assembly.IsElemAbelian 3 F ∧ Nat.card F = 27 ∧
    (∀ y ∈ F ⊓ L, y ≠ 1 → ∀ z ∈ F ⊓ L, z ≠ 1 → ∃ l ∈ L, l * y * l⁻¹ = z) ∧
    F ≤ Subgroup.normalizer (E : Set G)

end CFSG.RankThree.PartTwo.Sec13
