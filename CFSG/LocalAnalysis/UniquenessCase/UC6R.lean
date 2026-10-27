module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

@[expose] def R6_1 (D : Data G) : Prop :=
  ∀ p ∈ D.sig, ∀ X : Subgroup G, X ≤ D.M → IsPGroup p X → ¬ IsCyclic X → UniqueMax D.M X

@[expose] def R6_3 (D : Data G) : Prop :=
  ∀ r : ℕ, r.Prime → r ≠ 2 → ∀ E : Subgroup G, E ≤ D.M → CFSG.Open.IsElemAbelian r E →
    Nat.card E = r ^ 2 → rankThreeGamma 1 r E ≤ D.M → UniqueMax D.M E

@[expose] def R6_6 (D : Data G) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 →
    ((IsStronglyPEmbedded p D.M ∨ p ∈ D.sig) →
      ∀ N ∈ calMOf D.T, 2 ≤ CFSG.Open.pRank p N → N = D.M) ∧
    (∀ N : Subgroup G, rankThreeIsMaxTwoLocal N → 4 ≤ CFSG.Open.pRank p N →
      2 ≤ CFSG.Open.pRank p (D.M ⊓ N) →
      N = D.M) ∧
    (p = 3 → ∀ N ∈ calMOf D.T, 4 ≤ CFSG.Open.pRank 3 N → N = D.M)

@[expose] def R6_10 (D : Data G) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ P : Sylow p G, ∀ Y : Subgroup G, Y ≤ (P : Subgroup G) →
    (Y.subgroupOf (P : Subgroup G)).Normal → ¬ IsCyclic Y → (∀ y ∈ Y, y ^ p = 1) →
    rankThreeGamma 1 p Y ≤ D.M → ∀ X : Subgroup G, X ≤ D.M → IsPGroup p X →
    normalizer (X : Set G) ≤ D.M → ∀ g : G, g ∉ D.M → X ≤ uniqueFourConj g D.M →
    (∃ a ∈ D.M, ∃ b ∈ D.M, ∃ A B E : Subgroup G,
      Nat.card A = p ∧ Nat.card B = p ∧ A ≤ uniqueFourConj a Y ∧ B ≤ uniqueFourConj (b * g) Y ∧
      CFSG.Open.IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧ A ⊔ B = E ∧
      E = (uniqueFourConj a Y ⊓ uniqueFourConj g D.M) ⊔
        (uniqueFourConj (b * g) Y ⊓ D.M) ∧
      ∃ φ : ↥((uniqueFourConj a Y ⊓ normalizer (E : Set G)) ⊔
          (uniqueFourConj (b * g) Y ⊓ normalizer (E : Set G))) →* SL(2, ZMod p),
        Function.Surjective φ ∧
          φ.ker = (centralizer (E : Set G)).subgroupOf
            ((uniqueFourConj a Y ⊓ normalizer (E : Set G)) ⊔
              (uniqueFourConj (b * g) Y ⊓ normalizer (E : Set G))))
    ∧ ∀ V : Subgroup G, InCalV D.M V → ¬ V ≤ uniqueFourConj g D.M

@[expose] def R6_14 (D : Data G) : Prop :=
  D.sig ⊆ D.sig1 → ∀ r : ℕ, r.Prime → r ≠ 2 → r ∉ D.sig →
    ∀ R : Subgroup G, CFSG.ABGLocalTools.IsSylowOf r R D.M →
      ∀ E : Subgroup G, E ≤ R ⊓ centralizer (R : Set G) → CFSG.Open.IsElemAbelian r E →
        Nat.card E = r ^ 2 → rankThreeGamma 1 r E ≤ D.M → IsStronglyPEmbedded r D.M

end CFSG.LocalAnalysis.UniquenessCase.UC6
