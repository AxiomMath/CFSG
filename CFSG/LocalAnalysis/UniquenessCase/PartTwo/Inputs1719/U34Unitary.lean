module

public import CFSG.Quasithin.Background.HSU3Unitary
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.SU3
open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Matrix

@[expose] def K_U34NormalizerRanks : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 16 →
    Nat.card (natNorm (StatedSU 3 4 K)) = 2 ^ 8 * 3 ^ 2 * 5 ^ 3 * 13 ∧
      pRank 2 (⊤ : Subgroup (natNorm (StatedSU 3 4 K))) = 3 ∧
      pRank 3 (⊤ : Subgroup (natNorm (StatedSU 3 4 K))) = 2 ∧
      pRank 5 (⊤ : Subgroup (natNorm (StatedSU 3 4 K))) = 3 ∧
      pRank 13 (⊤ : Subgroup (natNorm (StatedSU 3 4 K))) = 1

@[expose] def u34FiveScalar (K : Type) [Field K] : Subgroup (MulAut (StdMod (Fin 3) K)) :=
  pCoreOf 5 (natImage (StatedScalars (Fin 3) K))

@[expose] def K_U34FiveResidual : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 16 →
    ∀ X : Subgroup (MulAut (StdMod (Fin 3) K)),
      natImage (StatedSU 3 4 K) ≤ X → X ≤ natNorm (StatedSU 3 4 K) →
        Opp 5 X = natImage (StatedSU 3 4 K) ∨
          Opp 5 X = natImage (StatedSU 3 4 K) ⊔ u34FiveScalar K

@[expose] def K_U34NonsingularStab : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 16 →
    ∀ v : Fin 3 → K, v ≠ 0 → herm 2 v v ≠ 0 →
      ∃ x : StatedSU 3 4 K, orderOf x = 5 ∧
        (((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) *ᵥ v = v

@[expose] def K_U34Hermitian : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 16 →
    ∀ U : AddSubgroup (Fin 3 → K),
      (∀ v ∈ U, herm 2 v v = 0) → Nat.card U ≤ 16

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
