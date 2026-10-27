module

public import CFSG.RankThree.PartOne.S12.BaseNodes

public section

namespace CFSG.RankThree.PartOne

structure Sec12Facts (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G)
    (L E : Subgroup G) : Prop where
  two : Sec12TwoGeneric p c L E ∨ Sec12TwoSU5 p c L E
  twoB : cNormalizer c ⊓ torusNormalizer E ≤ Subgroup.normalizer (L : Set G)
  three : torusImage E L =
      Subgroup.closure (reflectionSet p E ∩ (torusImage E L : Set (MulAut E))) ∧
    ∃ r : ℕ, 1 ≤ r ∧ r ≤ 12 ∧ RowModel p L r ∧ RowWeylIso E (torusImage E L) r ∧
      (r ≤ 8 → E = A) ∧ (9 ≤ r → Nat.card E = p ^ 4)
  four : (∀ B : Subgroup G, B ≤ E → torusInvariant E L B → B ≠ ⊥ → B ≠ E →
      B = Subgroup.zpowers c ∨ B = ⁅E, L ⊓ torusNormalizer E⁆) ∧
    ((E = Subgroup.zpowers c ⊔ ⁅E, L ⊓ torusNormalizer E⁆ ∧
        Subgroup.zpowers c ⊓ ⁅E, L ⊓ torusNormalizer E⁆ = ⊥) ∨
      ((RowModel p L 11 ∧ RowWeylIso E (torusImage E L) 11) ∧ ⁅E, L ⊓ torusNormalizer E⁆ = E))
  five : ¬ torusNormalizer E ≤ cNormalizer c

theorem Sec12Facts.of_nodes (h122 : Node122) (h122b : Node122b) (h123 : Node123)
    (h124 : Node124) (h125 : Node125) {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G}
    {c : G} {L E : Subgroup G} (h : Sec12Hyp G p A c L E) : Sec12Facts G p A c L E :=
  ⟨h122 G p A c L E h, h122b G p A c L E h, h123 G p A c L E h, h124 G p A c L E h,
    h125 G p A c L E h⟩

end CFSG.RankThree.PartOne
