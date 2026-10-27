module

public import CFSG.RankThree.GF2n.Basic

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def IsMaxRootWitness (M B : Subgroup G) (g : G) : Prop :=
  ¬ conjSubgroup g B ≤ M ∧ conjSubgroup g B ⊓ M ≠ ⊥ ∧
    ∀ h : G, ¬ conjSubgroup h B ≤ M → conjSubgroup h B ⊓ M ≠ ⊥ →
      Nat.card ↥(conjSubgroup h B ⊓ M) ≤ Nat.card ↥(conjSubgroup g B ⊓ M)

@[expose] def RootStep1 (M B Q : Subgroup G) (g : G) : Prop :=
  ∀ a ∈ conjSubgroup g B ⊓ M, a ≠ 1 → ∀ y ∈ Q, ⁅a, y⁆ ∈ B → y ^ 2 = 1

@[expose] def RootStep1Case2 (M B Q : Subgroup G) (g : G) : Prop :=
  ∀ a ∈ conjSubgroup g B ⊓ M, a ≠ 1 → ∀ y ∈ Q, ⁅a, y⁆ ∈ B → ⁅a, y⁆ ≠ 1 → y ^ 2 = 1

@[expose] def CitedT79 (B Q : Subgroup G) : Prop :=
  ∀ K : Subgroup G, Q ≤ K → inSubgroup (pCore 2) K ≠ ⊥ → B ≤ inSubgroup (pCore 2) K

structure Case2 (M B Q : Subgroup G) (g a y : G) : Prop where
  hgM : ¬ conjSubgroup g B ≤ M
  ha : a ∈ conjSubgroup g B ⊓ M
  ha1 : a ≠ 1
  hy : y ∈ Q
  hb : ⁅a, y⁆ ∈ B
  hb1 : ⁅a, y⁆ ≠ 1

end CFSG.RankThree.GF2n.Tim78
