module

public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
public import CFSG.RankThree.PartTwo.Sec19.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.AGLEmbedding (Asc81bHyp IsWeakSBlock NineThreeConclusion)
open CFSG.Assembly.RankThreeEven (projSU)

@[expose] def Item316 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    CFSG.Assembly.KProper CFSG.Assembly.InCatalog G → CFSG.Assembly.IsCharTwoType G →
    CFSG.Assembly.evenRank G = 3 →
    ∀ M L : Subgroup G, CFSG.IsMaximalTwoLocal M → IsScriptLBlock M L →
      CFSG.Assembly.InCatalog G

@[expose] def IsSmall194 (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* alternatingGroup (Fin 6)) ∨ Nonempty (X ≃* projSU 3 3 1)

@[expose] def Census194 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S K : Subgroup G), CFSG.Open.IsKGroup ↥X →
    Asc81bHyp X S → IsWeakSBlock X S K → NineThreeConclusion X S K →
    (∀ L : Subgroup G, ¬ IsScriptLBlock X L) →
    (∀ p : ℕ, p.Prime → 3 < p → CFSG.Open.pRank p X ≤ 2) → CFSG.Open.pRank 3 X ≤ 3 →
      (IsList194 (K ⧸ CFSG.pCore 2 K) ∨ IsSmall194 (K ⧸ CFSG.pCore 2 K)) ∧
      ((IsEmpty (K ⧸ CFSG.pCore 2 K ≃* alternatingGroup (Fin 10)) ∧
          IsProperParabolic (starIm K (Subgroup.normalizer (S : Set G)))) ∨
        (Nonempty (K ⧸ CFSG.pCore 2 K ≃* alternatingGroup (Fin 10)) ∧
          Sec4.IsExtOf (starIm K (Subgroup.normalizer (S : Set G))) (Equiv.Perm (Fin 5))
            (Multiplicative (Fin 4 → ZMod 2))))

@[expose] def Item194UsedWide : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Sec19Std G →
    ∀ A M H : Subgroup G, IsE27 A → M ∈ scriptM (gamma 2 A : Set G) →
      H ∈ scriptM (A : Set G) → H ≠ M →
      (scriptJ M H).Nonempty ∧
      ∀ K ∈ scriptJ M H,
        (IsList194 (K ⧸ CFSG.pCore 2 K) ∨ IsSmall194 (K ⧸ CFSG.pCore 2 K)) ∧
        ((IsEmpty (K ⧸ CFSG.pCore 2 K ≃* alternatingGroup (Fin 10)) ∧
            IsProperParabolic (starIm K H)) ∨
          (Nonempty (K ⧸ CFSG.pCore 2 K ≃* alternatingGroup (Fin 10)) ∧
            Sec4.IsExtOf (starIm K H) (Equiv.Perm (Fin 5)) (Multiplicative (Fin 4 → ZMod 2))))

@[expose] def Item194NoSmall : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Sec19Std G →
    ∀ A M H : Subgroup G, IsE27 A → M ∈ scriptM (gamma 2 A : Set G) →
      H ∈ scriptM (A : Set G) → H ≠ M →
      ∀ K ∈ scriptJ M H, ¬ IsSmall194 (K ⧸ CFSG.pCore 2 K)

end CFSG.RankThree.PartTwo.Sec19
