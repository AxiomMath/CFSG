module

public import CFSG.RankThree.PartTwo.Sec21.Notation
public import CFSG.RankThree.PartTwo.Sec7.ThreeTranspositions

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU localRank)

@[expose] def Item226CentralReflection : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Nat.card A = 3 ^ 4 →
      ∀ d ∈ dStar A, (∀ x ∈ starOf A L, x * d = d * x) →
        (commOf d).map A.subtype = Subgroup.zpowers c ∧
          ∀ d' ∈ dStar A, (∀ x ∈ starOf A L, x * d' = d' * x) → d' = d

@[expose] def Item226LocalSetS3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Nat.card A = 3 ^ 4 →
      (∀ φ ∈ dStar A, ∀ ψ ∈ dStar A, ∃ g ∈ Subgroup.closure (dStar A), g * φ * g⁻¹ = ψ) →
      ∀ t ∈ dStar A,
        Nonempty (Subgroup.closure (Sec7.localSet (dStar A) t) ≃* Equiv.Perm (Fin 3))

@[expose] def Item226OThreeCentral : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Nat.card A = 3 ^ 4 →
      (∀ φ ∈ dStar A, ∀ ψ ∈ dStar A, ∃ g ∈ Subgroup.closure (dStar A), g * φ * g⁻¹ = ψ) →
      (∀ t ∈ dStar A,
        Nonempty (Subgroup.closure (Sec7.localSet (dStar A) t) ≃* Equiv.Perm (Fin 3))) →
      CFSG.pCore 3 (Subgroup.closure (dStar A)) ≤ Subgroup.center (Subgroup.closure (dStar A))

@[expose] def CentralExtensionTrivial226 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Group.IsPerfect X →
    ∀ n : ℕ, 1 < n → Odd n →
      Nonempty (X ⧸ Subgroup.center X ≃* projSU 5 2 n) → Subgroup.center X = ⊥

@[expose] def LocalRankLowerBound226 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 1 < n → Odd n → n ≠ 3 →
    Nonempty (X ≃* projSU 5 2 n) → ∃ p : ℕ, p.Prime ∧ 3 < p ∧ 3 ≤ localRank p X

end CFSG.RankThree.PartTwo.Sec21
