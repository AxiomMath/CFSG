module

public import CFSG.RankThree.PartTwo.Sec21.Item223KFactsProofInsp

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)

@[expose] def Inspection223ListInner : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X A B K : Subgroup G) (m : ℕ),
    Sec4.IsList46 (X ⧸ aschbacherSolvableCore 3 X) →
    CFSG.Assembly.IsElemAbelian 3 A → Nat.card A = 3 ^ 4 →
    A ≤ Subgroup.normalizer (X : Set G) →
    Nat.card (A ⊓ Sec4.thetaQuotCentralizer X : Subgroup G) = 3 →
    (∀ x ∈ A, ¬ Sec4.InducesOuterTheta x X) →
    B ≤ A → Nat.card B = 3 ^ 3 → K ≤ X → K ≤ Subgroup.centralizer (B : Set G) →
    (∀ y ∈ X ⊓ Subgroup.centralizer (B : Set G), ∀ k ∈ K, y * k * y⁻¹ ∈ K) →
    Nonempty (K ≃* projSL 2 (GaloisField 2 m)) → 1 < m → Odd m →
    ∃ k : ℕ, Odd k ∧ Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* projSU 4 2 k)


@[expose] def Inspection223ListOuter : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X A : Subgroup G),
    Sec4.IsList46 (X ⧸ aschbacherSolvableCore 3 X) →
    CFSG.Assembly.IsElemAbelian 3 A → Nat.card A = 3 ^ 4 →
    A ≤ Subgroup.normalizer (X : Set G) →
    Nat.card (A ⊓ Sec4.thetaQuotCentralizer X : Subgroup G) = 3 →
    (∀ x ∈ A, Sec4.InducesOuterTheta x X → KFacts.InducesStdKind X x .diagonal) →
    ∀ x ∈ A, ¬ Sec4.InducesOuterTheta x X

theorem inspection223List_of (hInner : Inspection223ListInner)
    (hOuter : Inspection223ListOuter) : Inspection223List := by
  intro G _ _ X A B K m hL hAe hA81 hAN hAC hdiag hBA hB27 hKX hKC hKN hK hm1 hmo
  exact hInner G X A B K m hL hAe hA81 hAN hAC (hOuter G X A hL hAe hA81 hAN hAC hdiag) hBA hB27
    hKX hKC hKN hK hm1 hmo

end CFSG.RankThree.PartTwo.Sec21
