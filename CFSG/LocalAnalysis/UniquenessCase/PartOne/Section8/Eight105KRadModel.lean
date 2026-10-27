module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KRadDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KRadSideA
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KRadSideB
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KRadUniq

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K105

open CFSG.Open Subgroup
open CFSG.Assembly.LowTwoRank (StatedSU)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f ε : ℕ}
  {b : StatedSU (2 * 2 + ε) (2 ^ f) K} {ω : K}

theorem RadSetup.radicalFacts (hS : RadSetup ε b ω) (h : UnitaryFieldData 2 f K)
    (hK₀ : F08.KOf8103 ⊤ (zpowers b) ≠ ⊥) :
    RadicalFacts (StatedSU (2 * 2 + ε) (2 ^ f) K) (zpowers b) := by
  have key : ∀ {μ : K}, RadSetup ε b μ →
      stabSU (2 ^ f) (eigSU b μ) ≠ ⊤ ∧
        (∃ T₀ : Sylow 2 (StatedSU (2 * 2 + ε) (2 ^ f) K),
          normalizer ((T₀ : Subgroup (StatedSU (2 * 2 + ε) (2 ^ f) K)) :
            Set (StatedSU (2 * 2 + ε) (2 ^ f) K)) ≤
            stabSU (2 ^ f) (eigSU b μ)) ∧
        centralizer ((zpowers b : Subgroup _) : Set (StatedSU (2 * 2 + ε) (2 ^ f) K)) ≤
          stabSU (2 ^ f) (eigSU b μ) ∧
        pCoreOf 2 (stabSU (2 ^ f) (eigSU b μ)) ≠ ⊥ ∧
        F08.KOf8103 ⊤ (zpowers b) ⊓ pCoreOf 2 (stabSU (2 ^ f) (eigSU b μ)) = ⊥ ∧
        ∀ T₀ : Sylow 2 (StatedSU (2 * 2 + ε) (2 ^ f) K),
          pCoreOf 2 (stabSU (2 ^ f) (eigSU b μ)) ≤ T₀ →
            normalizer ((T₀ : Subgroup (StatedSU (2 * 2 + ε) (2 ^ f) K)) :
              Set (StatedSU (2 * 2 + ε) (2 ^ f) K)) ≤
              stabSU (2 ^ f) (eigSU b μ) := fun hμ =>
    ⟨hμ.stabSU_ne_top h, hμ.exists_normalizer_le h, centralizer_le_stabSU_eigSU b _,
      hμ.pCoreOf_ne_bot h, hμ.kOf_inf_pCoreOf_eq_bot h hK₀,
      fun T₀ hT₀ => hμ.normalizer_le_of_pCoreOf_le h T₀ hT₀⟩
  refine ⟨stabSU (2 ^ f) (eigSU b ω), stabSU (2 ^ f) (eigSU b ω⁻¹), ?_,
    hS.pCoreOf_inf_stabSU_eq_bot h hK₀, ?_, fun Z hZ hN hKZ => hS.eq_or_eq_of_le h hK₀ hZ hN hKZ⟩
  · rintro Y (rfl | rfl)
    · exact key hS
    · exact key hS.symm
  · simpa only [inv_inv] using hS.symm.pCoreOf_inf_stabSU_eq_bot h hK₀

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K105
