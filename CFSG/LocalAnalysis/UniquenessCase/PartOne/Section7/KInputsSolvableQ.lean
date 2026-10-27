module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvable
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.A15LocalSect

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.AGLEmbedding.A15Local.Sect (SectionsOrder60)

@[expose] def StronglyEmbeddedSolvableQ : Prop :=
  ∀ p : ℕ, p.Prime → 5 ≤ p →
    ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → CFSG.pPrimeCore p X = ⊥ →
      2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) → ∀ N : Subgroup X, IsStronglyPEmbedded p N →
        ¬ CoverHasLargeTwoLocal ↥(CFSG.generalizedFitting X) →
        IsSolvable ↥N ∨ (p = 5 ∧ (Nat.card N).factorization 5 ≤ 2 ∧
          (∀ Y : Subgroup X, Y ≤ N → ⁅Y, Y⁆ = Y → Nat.card Y ≤ 3600) ∧
          ∀ Y : Subgroup X, Y ≤ N → ⁅Y, Y⁆ = Y → SectionsOrder60 ↥Y)

theorem StronglyEmbeddedSolvableQ.toStronglyEmbeddedSolvable (h : StronglyEmbeddedSolvableQ) :
    StronglyEmbeddedSolvable := by
  intro p hp h5 X _ _ hX hO h2 N hN hD
  rcases h p hp h5 X hX hO h2 N hN hD with hs | ⟨hp5, hN5, hY, -⟩
  · exact Or.inl hs
  · exact Or.inr ⟨hp5, hN5, hY⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
