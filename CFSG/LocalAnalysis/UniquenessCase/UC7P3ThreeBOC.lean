module

public import CFSG.LocalAnalysis.UniquenessCase.UC7P3Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3ThreeSolv

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open CFSG.AGLEmbedding
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  (Gls3StronglyThreeEmbeddedPlus)

@[expose] def StronglyEmbeddedThreeBOC : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → CFSG.pPrimeCore 3 X = ⊥ →
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) → ∀ N : Subgroup X, IsStronglyPEmbedded 3 N →
      CoverActsTriviallyOnSmall 3 ↥(CFSG.generalizedFitting X) ∧
        Nat.card ↥(CFSG.pPrimeCore 3 ↥N) ≤ 2 ∧
        CentralizerHasPElementOutside 3 N

theorem StronglyEmbeddedThree_of_BOC (hG3 : Gls3StronglyThreeEmbeddedPlus)
    (hSch : KFactCatalogSchreier) (hBOC : StronglyEmbeddedThreeBOC) : StronglyEmbeddedThree :=
  fun X _ _ hX hO h2 N hN =>
    let ⟨hB, hOc, hC⟩ := hBOC X hX hO h2 N hN
    ⟨hB, hOc, hC, isSolvable_of_isStronglyPEmbedded_three hG3 hSch hX hO h2 hN⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
