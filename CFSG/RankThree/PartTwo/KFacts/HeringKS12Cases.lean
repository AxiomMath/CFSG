module

public import CFSG.RankThree.PartTwo.KFacts.KS12Covers
public import CFSG.RankThree.PartTwo.KFacts.HeringKS12McL
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSU localRank)

@[expose] def KS12Concl (X : Type) [Group X] [Finite X] : Prop :=
  3 ≤ localRank 3 X ∨
    ∃ E F T : Subgroup X, E ≤ F ∧ CFSG.Assembly.IsElemAbelian 3 F ∧ Nat.card E = 9 ∧
      Nat.card F = 27 ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧ E ≤ Subgroup.normalizer (T : Set X)

@[expose] def KS12CoverG2 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X → Nat.card (Subgroup.center X) = 3 →
    Blueprint.ChevalleyExceptionalModel (X ⧸ Subgroup.center X) .G2 3 1 → KS12Concl X

@[expose] def KS12CoverU4 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X → Nat.card (Subgroup.center X) = 3 →
    Nonempty (X ⧸ Subgroup.center X ≃* projSU 4 3 1) → KS12Concl X

@[expose] def KS12CoverJ3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X → Nat.card (Subgroup.center X) = 3 →
    Nonempty (X ⧸ Subgroup.center X ≃* Blueprint.NativeSporadic.J3) → KS12Concl X

@[expose] def KS12CoverON : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X → Nat.card (Subgroup.center X) = 3 →
    Nonempty (X ⧸ Subgroup.center X ≃* Blueprint.NativeSporadic.ON) → KS12Concl X

theorem ks12CoverExclusion_of_cases
    (hG2 : KS12CoverG2) (hU4 : KS12CoverU4) (hJ3 : KS12CoverJ3) (hON : KS12CoverON) :
    KS12CoverExclusion := by
  intro X _ _ hq hZ hX
  rcases hX with hG | hU | hJ | hM | hO
  · exact hG2 X hq hZ hG
  · exact hU4 X hq hZ hU
  · exact hJ3 X hq hZ hJ
  · obtain ⟨e⟩ := hM
    exact Or.inl (three_le_localRank_of_mcl_cover hZ e)
  · exact hON X hq hZ hO

end CFSG.RankThree.PartTwo.KFacts
