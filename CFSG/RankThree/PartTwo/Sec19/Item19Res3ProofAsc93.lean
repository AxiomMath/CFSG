module

public import CFSG.RankThree.PartTwo.Sec19.Item194Inputs

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.AGLEmbedding (Asc81bHyp IsWeakSBlock NineThreeConclusion barM InClassXBlock
  NineThreeTwo NineThreeThree NineThreeFour NineThreeFive NineThreeEight IsClassicalTwoOrG2
  HasIrreducibleCommutatorQuotient blockV)

section Defs

variable {G : Type} [Group G]

@[expose] def NineThreeSixNat (X S L : Subgroup G) : Prop :=
  HasIrreducibleCommutatorQuotient L (blockV S L) ∧ ∃ n : ℕ, 5 ≤ n ∧
    Nonempty (↥(barM X L) ≃* alternatingGroup (Fin (2 * n))) ∧
    barM X (S ⊓ L) = CFSG.Open.pCoreOf 2 (barM X (Subgroup.normalizer (S : Set G) ⊓ L)) ∧
    CFSG.Open.IsElemAbelian 2 (barM X (S ⊓ L)) ∧ Nat.card (barM X (S ⊓ L)) = 2 ^ (n - 1) ∧
    Nonempty (↥(barM X (Subgroup.normalizer (S : Set G) ⊓ L)) ⧸
      CFSG.pCore 2 ↥(barM X (Subgroup.normalizer (S : Set G) ⊓ L)) ≃* Equiv.Perm (Fin n))

@[expose] def NineThreeSevenNat (X S L : Subgroup G) : Prop :=
  HasIrreducibleCommutatorQuotient L (blockV S L) ∧ ∃ n : ℕ, 3 ≤ n ∧
    Nonempty (↥(barM X L) ≃* alternatingGroup (Fin (4 * n))) ∧
    Nonempty (↥(barM X (Subgroup.normalizer (S : Set G) ⊓ L)) ⧸
      CFSG.pCore 2 ↥(barM X (Subgroup.normalizer (S : Set G) ⊓ L)) ≃* Equiv.Perm (Fin n))

end Defs

@[expose] def Asc81bNineThreeNat : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), CFSG.Open.IsKGroup ↥X →
    Asc81bHyp X S → IsWeakSBlock X S L →
      InClassXBlock L ∨ NineThreeTwo X S L ∨ (NineThreeThree X S L ∧ IsTypeScriptL L) ∨
        (NineThreeFour X S L ∧ IsA6Z3Type L) ∨ (NineThreeFive X L ∧ IsA7FourType L) ∨
        NineThreeSixNat X S L ∨ NineThreeSevenNat X S L ∨ (NineThreeEight X S L ∧ IsTypeScriptL L)

@[expose] def IsTripleA6 (X : Type) [Group X] : Prop :=
  Nat.card (Subgroup.center X) = 3 ∧
    Nonempty (X ⧸ Subgroup.center X ≃* alternatingGroup (Fin 6))

@[expose] def KS194ClassicalCensus : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.IsQuasisimple Y → CFSG.pCore 2 Y = ⊥ →
    IsClassicalTwoOrG2 (Y ⧸ Subgroup.center Y) →
    (∀ p : ℕ, p.Prime → 3 < p → CFSG.Open.pRank p (⊤ : Subgroup Y) ≤ 2) →
    CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 3 →
    ∀ (J : Subgroup Y) (T : Sylow 2 Y), J ≠ ⊤ →
      Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J →
      Nat.card (CFSG.Open.pCoreOf 2 J) ≠ Nat.card T →
      (IsList194 Y ∨ IsSmall194 Y ∨ IsTripleA6 Y) ∧ IsEmpty (Y ≃* alternatingGroup (Fin 10))

@[expose] def Census194Wide : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S K : Subgroup G), CFSG.Open.IsKGroup ↥X →
    Asc81bHyp X S → IsWeakSBlock X S K → NineThreeConclusion X S K →
    (∀ L : Subgroup G, ¬ IsScriptLBlock X L) →
    (∀ p : ℕ, p.Prime → 3 < p → CFSG.Open.pRank p X ≤ 2) → CFSG.Open.pRank 3 X ≤ 3 →
      (IsList194 (K ⧸ CFSG.pCore 2 K) ∨ IsSmall194 (K ⧸ CFSG.pCore 2 K) ∨
          IsTripleA6 (K ⧸ CFSG.pCore 2 K)) ∧
      ((IsEmpty (K ⧸ CFSG.pCore 2 K ≃* alternatingGroup (Fin 10)) ∧
          IsProperParabolic (starIm K (Subgroup.normalizer (S : Set G)))) ∨
        (Nonempty (K ⧸ CFSG.pCore 2 K ≃* alternatingGroup (Fin 10)) ∧
          Sec4.IsExtOf (starIm K (Subgroup.normalizer (S : Set G))) (Equiv.Perm (Fin 5))
            (Multiplicative (Fin 4 → ZMod 2))))

@[expose] def Item194UsedWide3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Sec19Std G →
    ∀ A M H : Subgroup G, IsE27 A → M ∈ scriptM (gamma 2 A : Set G) →
      H ∈ scriptM (A : Set G) → H ≠ M →
      (scriptJ M H).Nonempty ∧
      ∀ K ∈ scriptJ M H,
        (IsList194 (K ⧸ CFSG.pCore 2 K) ∨ IsSmall194 (K ⧸ CFSG.pCore 2 K) ∨
            IsTripleA6 (K ⧸ CFSG.pCore 2 K)) ∧
        ((IsEmpty (K ⧸ CFSG.pCore 2 K ≃* alternatingGroup (Fin 10)) ∧
            IsProperParabolic (starIm K H)) ∨
          (Nonempty (K ⧸ CFSG.pCore 2 K ≃* alternatingGroup (Fin 10)) ∧
            Sec4.IsExtOf (starIm K H) (Equiv.Perm (Fin 5)) (Multiplicative (Fin 4 → ZMod 2))))

end CFSG.RankThree.PartTwo.Sec19
