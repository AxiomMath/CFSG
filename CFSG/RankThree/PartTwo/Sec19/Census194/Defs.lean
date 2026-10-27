module

public import CFSG.RankThree.PartTwo.Sec19.Item19Res3ProofAsc93
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusBase

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.Assembly.LowTwoRank
open CFSG.AGLEmbedding (IsSmallTwoOrG2)

structure Census194RankHyp (Y : Type) [Group Y] [Finite Y] : Prop where
  quasisimple : CFSG.IsQuasisimple Y
  pCore_two : CFSG.pCore 2 Y = ⊥
  pRank_prime : ∀ p : ℕ, p.Prime → 3 < p → CFSG.Open.pRank p (⊤ : Subgroup Y) ≤ 2
  pRank_three : CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 3

structure Census194Hyp (Y : Type) [Group Y] [Finite Y] (J : Subgroup Y) (T : Sylow 2 Y) : Prop
    extends Census194RankHyp Y where
  ne_top : J ≠ ⊤
  normalizer_le : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J
  card_ne : Nat.card (CFSG.Open.pCoreOf 2 J) ≠ Nat.card (T : Subgroup Y)

@[expose] def Census194SurvPSL : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (n f : ℕ), Census194RankHyp Y →
    StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSL n 2 f → 4 ≤ n →
    (n = 4 ∧ (f = 1 ∨ f = 2)) ∨ (f = 1 ∧ (n = 5 ∨ n = 6 ∨ n = 7))

@[expose] def Census194SurvPSU : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (n f : ℕ), Census194RankHyp Y →
    StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSU n 2 f → 4 ≤ n → n = 4 ∧ (f = 1 ∨ f = 3)

@[expose] def Census194SurvPSp : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (n f : ℕ), Census194RankHyp Y →
    StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSp n 2 f → 3 ≤ n → n = 3 ∧ f = 1

@[expose] def Census194SurvPOmegaPlus : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (n f : ℕ), Census194RankHyp Y →
    StatedClassicalModel (Y ⧸ Subgroup.center Y) .POmegaPlus n 2 f → False

@[expose] def Census194SurvPOmegaMinus : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (n f : ℕ), Census194RankHyp Y →
    StatedClassicalModel (Y ⧸ Subgroup.center Y) .POmegaMinus n 2 f → n = 4 ∧ f = 1

@[expose] def Census194IdPSL : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (n f : ℕ), Census194RankHyp Y →
    StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSL n 2 f → 3 ≤ n →
    (n = 3 ∨ (n = 4 ∧ (f = 1 ∨ f = 2)) ∨ (f = 1 ∧ (n = 5 ∨ n = 6 ∨ n = 7))) → IsList194 Y

@[expose] def Census194IdPSU : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (f : ℕ), Census194RankHyp Y →
    StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSU 4 2 f → (f = 1 ∨ f = 3) → IsList194 Y

@[expose] def Census194IdPSp : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (n f : ℕ), Census194RankHyp Y →
    StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSp n 2 f →
    (n = 2 ∨ (n = 3 ∧ f = 1)) → IsList194 Y

@[expose] def Census194IdPOmegaMinus : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], Census194RankHyp Y →
    StatedClassicalModel (Y ⧸ Subgroup.center Y) .POmegaMinus 4 2 1 → IsList194 Y

@[expose] def Census194IdG2 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (q : TauCeti.PrimePower), Census194RankHyp Y → q.p = 2 →
    Sec4.IsoGTwo (Y ⧸ Subgroup.center Y) q → IsList194 Y

@[expose] def Census194IdSmall : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (J : Subgroup Y) (T : Sylow 2 Y), Census194Hyp Y J T →
    IsSmallTwoOrG2 (Y ⧸ Subgroup.center Y) → IsList194 Y ∨ IsSmall194 Y ∨ IsTripleA6 Y

@[expose] def Census194RankOne : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (J : Subgroup Y) (T : Sylow 2 Y), Census194Hyp Y J T →
    (∀ f : ℕ, ¬ StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSL 2 2 f) ∧
    (∀ f : ℕ, ¬ StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSU 3 2 f) ∧
    IsEmpty (Y ⧸ Subgroup.center Y ≃* alternatingGroup (Fin 5))

end CFSG.RankThree.PartTwo.Sec19
