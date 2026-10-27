module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
import CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalCoverFiveModel
import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallOmegaSix
import CFSG.Open.StatedZModTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Adapters.RankTwoModelTransports CFSG.Assembly.LowTwoRank

theorem s15k_omp6_isAlt8 {X : Type} [Group X] (h : IsOmegaPlus X 6 1) : UC22.IsAlt X 8 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have hK2 : Nat.card K = 2 := by simpa using hK
  haveI : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = Fintype.card (ZMod 2) := by
    rw [← Nat.card_eq_fintype_card, hK2, ZMod.card]
  let φ : K ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq hc
  have hQ : ∀ v : Fin 3 ⊕ Fin 3 → K,
      StatedQuadPlus 3 (ZMod 2) (φ ∘ v) = φ (StatedQuadPlus 3 K v) := by
    intro v
    simp only [StatedQuadPlus, Function.comp_apply, map_sum, map_mul]
  have e0 : X ≃* StatedProj (StatedOmega (StatedQuadPlus 3 K)) := e
  have e1 : StatedProj (StatedOmega (StatedQuadPlus 3 K)) ≃*
      StatedProj (StatedOmega (StatedQuadPlus 3 (ZMod 2))) :=
    statedProjCongr (glCongr φ)
      (CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalCover.map_statedOmega φ hQ)
      (glCongr_statedScalars φ)
  have hbot : (StatedScalars (Fin 3 ⊕ Fin 3) (ZMod 2)).subgroupOf
      (StatedOmega (StatedQuadPlus 3 (ZMod 2))) = ⊥ := by
    rw [StatedAPI.statedScalars_eq_bot_of_card_two (by simp), Subgroup.bot_subgroupOf]
  have e2 : StatedProj (StatedOmega (StatedQuadPlus 3 (ZMod 2))) ≃*
      StatedOmega (StatedQuadPlus 3 (ZMod 2)) :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  exact ⟨e0.trans (e1.trans (e2.trans
    CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.statedOmega_quadPlus_three_mulEquiv_alt8))⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
