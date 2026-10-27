module

public import CFSG.RankThree.PartOne.S12.InputsTable

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure Sec12TwoGeneric (p : ℕ) (c : G) (L E : Subgroup G) : Prop where
  center_pPrime : ¬ p ∣ Nat.card (Subgroup.center L)
  quasisimple : CFSG.IsQuasisimple L
  localRank_eq : localRank p L = 2
  centralizer_rank : CFSG.pRank p ↥(Subgroup.centralizer (L : Set G)) = 1
  pElements : ∀ x : G, x ∈ cNormalizer c → orderOf x = p → x ∈ Subgroup.zpowers c ⊔ L
  E_eq : E = (E ⊓ L) ⊔ Subgroup.zpowers c

structure Sec12TwoSU5 (p : ℕ) (c : G) (L E : Subgroup G) : Prop where
  p_eq : p = 5
  quasisimple : CFSG.IsQuasisimple L
  center_eq : (Subgroup.center L).map L.subtype = Subgroup.zpowers c
  center_card : Nat.card (Subgroup.center L) = 5
  model : ∃ f : ℕ, 1 ≤ f ∧ StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 5 2 f
  E_le : E ≤ L
  contains_subgroups : ∀ X : Subgroup G, X ≤ cNormalizer c → Nat.card X = 5 →
    (∃ S : Subgroup G, S ≠ ⊥ ∧ IsPGroup 2 S ∧ S ≤ L ∧ X ≤ Subgroup.normalizer (S : Set G)) →
    X ≤ L

@[expose] def Node122 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → Sec12TwoGeneric p c L E ∨ Sec12TwoSU5 p c L E

@[expose] def Node122b : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E →
    cNormalizer c ⊓ torusNormalizer E ≤ Subgroup.normalizer (L : Set G)

@[expose] def Node123 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E →
    torusImage E L = Subgroup.closure (reflectionSet p E ∩ (torusImage E L : Set (MulAut E))) ∧
    ∃ r : ℕ, 1 ≤ r ∧ r ≤ 12 ∧ RowModel p L r ∧ RowWeylIso E (torusImage E L) r ∧
      (r ≤ 8 → E = A) ∧ (9 ≤ r → Nat.card E = p ^ 4)

@[expose] def Node124 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E →
    (∀ B : Subgroup G, B ≤ E → torusInvariant E L B → B ≠ ⊥ → B ≠ E →
      B = Subgroup.zpowers c ∨ B = ⁅E, L ⊓ torusNormalizer E⁆) ∧
    ((E = Subgroup.zpowers c ⊔ ⁅E, L ⊓ torusNormalizer E⁆ ∧
        Subgroup.zpowers c ⊓ ⁅E, L ⊓ torusNormalizer E⁆ = ⊥) ∨
      ((RowModel p L 11 ∧ RowWeylIso E (torusImage E L) 11) ∧ ⁅E, L ⊓ torusNormalizer E⁆ = E))

@[expose] def Node124b : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → p ∣ Nat.card (Subgroup.center L) → ⁅E, L ⊓ torusNormalizer E⁆ = E

@[expose] def Node125 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → ¬ torusNormalizer E ≤ cNormalizer c

end CFSG.RankThree.PartOne
