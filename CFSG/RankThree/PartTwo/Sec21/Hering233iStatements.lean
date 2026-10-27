module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore
public import CFSG.RankThree.PartTwo.KFacts.KS21Terminal

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

@[expose] def TerminalE16 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (I A : Subgroup G), A ≤ I → IsElemAbelian 3 A →
    ((Nonempty (I ≃* projSU 5 2 3) ∧ Nat.card A = 3 ^ 4) ∨
      (Nonempty (I ≃* projSL 4 (GaloisField 2 2)) ∧ Nat.card A = 3 ^ 3) ∨
      (Nonempty (I ≃* projSp 3 (GaloisField 2 2)) ∧ Nat.card A = 3 ^ 3)) →
    ∀ B : Subgroup G, B ≤ A → Nat.card B = 3 →
      ∀ X : Subgroup (I ⊓ Subgroup.centralizer (B : Set G) : Subgroup G),
        CFSG.IsComponent X →
        (∃ E : Subgroup G, E ≤ I ∧ IsElemAbelian 2 E ∧ Nat.card E = 2 ^ 4 ∧
            E ≤ Subgroup.normalizer (B : Set G) ∧
            E ≤ Subgroup.normalizer
              ((X.map (I ⊓ Subgroup.centralizer (B : Set G)).subtype : Subgroup G) : Set G)) ∨
          (Nonempty (I ≃* projSL 4 (GaloisField 2 2)) ∧ Nat.card A = 3 ^ 3 ∧
            (∀ X' : Subgroup (I ⊓ Subgroup.centralizer (B : Set G) : Subgroup G),
              CFSG.IsComponent X' → X' = X) ∧ Nat.card X = 60)

end CFSG.RankThree.PartTwo.Sec21
