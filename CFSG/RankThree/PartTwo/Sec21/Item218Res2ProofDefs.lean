module

public import CFSG.RankThree.PartTwo.Sec21.Item211

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)

@[expose] def Item2115LThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U₀ : Subgroup G) (a : G) (X : Subgroup G) (c : G),
    Sec21Pair G A E U₀ a X → U₀ ∈ fourGroupsMinus E →
    ((∃ n : ℕ, 0 < n ∧ Even n ∧
        ((Nonempty (lBar X ≃* projSL 3 (GaloisField 2 n)) ∧ Sec4.IsTypeCOn A X) ∨
          (Nonempty (lBar X ≃* SL3 n) ∧ IsTypeCOnBarSL A X))) ∧
      Nat.card A = 3 ^ 3 ∧ Nonempty (starOf A X ≃* Equiv.Perm (Fin 3))) →
    c ∈ A → c ∉ Subgroup.zpowers a → c ∈ Subgroup.centralizer (U₀ : Set G) →
    ¬ (X ⊓ Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers c : Set G))

@[expose] def Item2115U4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → (∃ n : ℕ, Odd n ∧ Nonempty (L ≃* projSU 4 2 n)) →
      ¬ Subgroup.normalizer (A : Set G) ≤
        Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G)

end CFSG.RankThree.PartTwo.Sec21
