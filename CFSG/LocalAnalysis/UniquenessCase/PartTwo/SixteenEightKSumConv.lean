module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKJPrimeLie
import CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalCoverFiveModel
import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallOmegaFour
import CFSG.Open.StatedZModTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Adapters.RankTwoModelTransports CFSG.Assembly.LowTwoRank

theorem s16k_isLn_of_isSLn {X : Type} [Group X] {n : ℕ} (hn : 3 ≤ n) (h : IsSLn X n 1) :
    IsLn X n 1 := by
  obtain ⟨K, hF, hfin, hcard, ⟨e⟩⟩ := h
  have hK2 : Nat.card K = 2 := by simpa using hcard
  obtain ⟨f⟩ := s15k_jp_projEquiv hK2 (StatedSL n K)
  refine Or.inl ⟨by decide, ⟨Nat.prime_two, le_rfl, by omega, ?_, ?_⟩, K, hF, hfin, hcard, ?_⟩
  · intro hc
    exact absurd (congrArg Prod.fst hc) (by omega)
  · intro hc
    exact absurd (congrArg Prod.fst hc) (by omega)
  · exact ⟨e.trans f.symm⟩

theorem s16k_isAlt_five_of_isOmegaMinus_four {X : Type} [Group X] (h : IsOmegaMinus X 4 1) :
    IsAlt X 5 := by
  obtain ⟨-, K, hF, hfin, b, c, hK, hirr, ⟨e⟩⟩ := h
  have hK2 : Nat.card K = 2 := by simpa using hK
  haveI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = Fintype.card (ZMod 2) := by
    rw [← Nat.card_eq_fintype_card, hK2, ZMod.card]
  let φ : K ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq hcard
  have hpoly' : ∀ t : ZMod 2, t ^ 2 + φ b * t + φ c ≠ 0 := by
    intro t h0
    apply hirr (φ.symm t)
    apply φ.injective
    simpa using h0
  have hbc : φ b = 1 ∧ φ c = 1 := by
    have h0 := hpoly' 0
    have h1 := hpoly' 1
    generalize φ b = x at h0 h1 ⊢
    generalize φ c = y at h0 h1 ⊢
    revert x y
    decide
  obtain ⟨hb, hc⟩ := hbc
  have hQ : ∀ v : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K,
      StatedQuadMinus 2 (ZMod 2) 1 1 (φ ∘ v) = φ (StatedQuadMinus 2 K b c v) :=
    fun v => CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalCover.statedQuadMinus_comp
      φ hb hc v
  have e0 : X ≃* StatedProj (StatedOmega (StatedQuadMinus 2 K b c)) := e
  have e1 : StatedProj (StatedOmega (StatedQuadMinus 2 K b c)) ≃*
      StatedProj (StatedOmega (StatedQuadMinus 2 (ZMod 2) 1 1)) :=
    statedProjCongr (glCongr φ)
      (CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalCover.map_statedOmega φ hQ)
      (glCongr_statedScalars φ)
  have hbot : (StatedScalars (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) (ZMod 2)).subgroupOf
      (StatedOmega (StatedQuadMinus 2 (ZMod 2) 1 1)) = ⊥ := by
    rw [StatedAPI.statedScalars_eq_bot_of_card_two (by simp), Subgroup.bot_subgroupOf]
  have e2 : StatedProj (StatedOmega (StatedQuadMinus 2 (ZMod 2) 1 1)) ≃*
      StatedOmega (StatedQuadMinus 2 (ZMod 2) 1 1) :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  exact ⟨e0.trans (e1.trans (e2.trans
    CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.statedOmega_quadMinus_two_mulEquiv_alt5))⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
