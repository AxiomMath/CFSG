module

public import CFSG.RankThree.PartTwo.Sec4.Vocabulary
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSU localRank)

@[expose] def KS12CoverExclusion : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X → Nat.card (Subgroup.center X) = 3 →
    (Blueprint.ChevalleyExceptionalModel (X ⧸ Subgroup.center X) .G2 3 1 ∨
      Nonempty (X ⧸ Subgroup.center X ≃* projSU 4 3 1) ∨
      Nonempty (X ⧸ Subgroup.center X ≃* Blueprint.NativeSporadic.J3) ∨
      Nonempty (X ⧸ Subgroup.center X ≃* Blueprint.NativeSporadic.McL) ∨
      Nonempty (X ⧸ Subgroup.center X ≃* Blueprint.NativeSporadic.ON)) →
    3 ≤ localRank 3 X ∨
      ∃ E F T : Subgroup X, E ≤ F ∧ CFSG.Assembly.IsElemAbelian 3 F ∧ Nat.card E = 9 ∧
        Nat.card F = 27 ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧ E ≤ Subgroup.normalizer (T : Set X)

@[expose] def KS12NormalizerMoves : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X →
    (Sec4.IsSLThreePi X ∨ Sec4.IsTripleCover X (alternatingGroup (Fin 6)) ∨
      Sec4.IsTripleCover X (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover X Blueprint.NativeSporadic.M22) →
    ∀ T : Subgroup X, CFSG.Assembly.IsElemAbelian 3 T → Nat.card T = 9 →
      Subgroup.center X ≤ T →
        ∃ x ∈ Subgroup.normalizer (T : Set X), IsPGroup 3 (Subgroup.zpowers x) ∧
          ∃ t ∈ T, x * t * x⁻¹ ≠ t

end CFSG.RankThree.PartTwo.KFacts
