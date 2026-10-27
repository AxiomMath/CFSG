module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront08

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)

variable {G : Type} [Group G] [Finite G]

@[expose] def R8103At (D : Data G) (L P : Subgroup G) (p n : ℕ) : Prop :=
  Even n ∧ ((2 : ℤ) ^ n ≡ -1 [ZMOD p] ∧ evenRank G = 3) ∧
  (∀ q : ℕ, q.Prime → q ∣ 2 ^ n + 1 → IsStronglyPEmbedded q D.M) ∧
  (∃ A : Subgroup G, F08.NotationA8103 L P p n A) ∧
  (∃ B : Subgroup G, F08.NotationB8103 L P n B) ∧
  (∀ A : Subgroup G, F08.NotationA8103 L P p n A → A ∈ uniqueSet D.M) ∧
  (∀ B : Subgroup G, F08.NotationB8103 L P n B → ¬ centralizer (B : Set G) ≤ D.M) ∧
  CFSG.ABGLocalTools.IsSylowOf 3 P ⊤

@[expose] def R8106At (D : Data G) (L P : Subgroup G) (n : ℕ) : Prop :=
  ∀ B : Subgroup G, F08.NotationB8103 L P n B →
    pCoreOf 2 D.M ⊓ centralizer (B : Set G) = ⊥

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
