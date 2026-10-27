module

public import CFSG.Quasithin.EmptyFaithful.S142Bridge
public import CFSG.Quasithin.EmptyFaithful.S1421Final

public section

namespace CFSG.Quasithin

open CFSG.Open

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

namespace Hyp1421

theorem facts1422 (h11 : StageLemma14111) (h113 : StageLemma14113) (h : Hyp1421 G T M) :
    Facts1422 T M := by
  have hyp := h.hyp14118 h11
  obtain ⟨ht, hmmc⟩ := Hyp14118.lemma_14_1_18_two h113 hyp
  obtain ⟨-, ⟨e⟩, hOY⟩ := lemma_14_1_18_three h113 hyp rfl rfl
  have h4 := lemma_14_1_18_four h113 hyp rfl rfl
  obtain ⟨-, -, -, -, hm3⟩ := lemma_14_1_18_five h113 hyp rfl rfl
  refine ⟨ht, hmmc, ?_, hOY, h4, h.inf_centralizer_eq_pCoreOf h11 h113,
    h.nonempty_oTwoQuot_mulEquiv h11 h113, hm3⟩
  have hc : Nat.card (Multiplicative (ZMod 3)) = 3 := by simp
  exact (Nat.card_congr e.toEquiv).trans hc

end Hyp1421

theorem facts1422Input_of_stages (h11 : StageLemma14111) (h113 : StageLemma14113) :
    Facts1422Input := fun _ _ _ _ _ h => h.facts1422 h11 h113

theorem stageTheorem1427_of_stages_legacyBare (h11 : StageLemma14111) (h113 : StageLemma14113)
    (hE22 : E22Input) (h311 : Theorem311) (h13 : Lemma14213) (hf : Hyp111fInput)
    (h15 : Lemma14215) (hF112 : F112LegacyPrintedError) (hRO : RankOneListedFacts.{0})
    (htail : Lemma14216TailLegacyBare) (h17 : Lemma14217J2LegacyBare) (h18 : Lemma14218D4LegacyBare) (hI47 : I47Statement)
    (hF431 : F431D4) (hD4 : TrialityD4Bridge) : StageTheorem1427 :=
  stageTheorem1427_of_inputs_legacyBare (facts1422Input_of_stages h11 h113) hE22 h311 h13 hf h15 hF112 hRO
    htail h17 h18 hI47 hF431 hD4


theorem stageTheorem1427_of_stages (h11 : StageLemma14111) (h113 : StageLemma14113)
    (hE22 : E22Input) (h311 : Theorem311) (h13 : Lemma14213) (hf : Hyp111fInput)
    (h15 : Lemma14215) (hF112 : F112Statement) (hRO : RankOneListedFacts.{0})
    (htail : Lemma14216Tail) (h17 : Lemma14217J2) (h18 : Lemma14218D4) (hI47 : I47Statement)
    (hF431 : F431D4) (hD4 : TrialityD4Bridge) : StageTheorem1427 :=
  stageTheorem1427_of_inputs (facts1422Input_of_stages h11 h113) hE22 h311 h13 hf h15 hF112 hRO
    htail h17 h18 hI47 hF431 hD4

end CFSG.Quasithin
