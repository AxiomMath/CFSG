module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

@[expose] def StronglyEmbeddedSolvableAltTen : Prop :=
  ∀ p : ℕ, p.Prime → 5 ≤ p →
    ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → CFSG.pPrimeCore p X = ⊥ →
      2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) → ∀ N : Subgroup X, IsStronglyPEmbedded p N →
        ¬ CoverHasLargeTwoLocal ↥(CFSG.generalizedFitting X) →
        IsSolvable ↥N ∨
          (p = 5 ∧ Nonempty (↥(CFSG.generalizedFitting X) ≃* alternatingGroup (Fin 10)) ∧
            ∀ Y : Subgroup X, Y ≤ N → ⁅Y, Y⁆ = Y → Y ≤ CFSG.generalizedFitting X ∧
              ∃ f : ↥Y →* alternatingGroup (Fin 5) × alternatingGroup (Fin 5),
                Function.Injective f)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
