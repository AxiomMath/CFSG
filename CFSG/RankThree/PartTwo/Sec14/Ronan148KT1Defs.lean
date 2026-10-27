module

public import CFSG.RankThree.PartTwo.Sec4.Item47Inputs

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148K

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

@[expose] def Row143 (S : Type) [Group S] [Finite S] : Prop :=
  ∀ (β : MulAut S), β ^ 3 = 1 → β ≠ 1 →
  ∀ (D : Subgroup S), D ≤ Sec4.autFix β → (D.subgroupOf (Sec4.autFix β)).Normal →
    (∀ x ∈ Sec4.autFix β, ∃ n : ℕ, x ^ (3 ^ n) ∈ D) →
  ∀ (P : Subgroup (MulAut S)), IsKGroup ↥P → P ≤ Subgroup.centralizer {β} →
    (∀ d ∈ D, MulAut.conj d ∈ Subgroup.normalizer (P : Set (MulAut S))) →
    Group.IsPerfect ↥P → ¬ 3 ∣ Nat.card ↥P → P = ⊥

end CFSG.RankThree.PartTwo.Sec14.Ronan148K
