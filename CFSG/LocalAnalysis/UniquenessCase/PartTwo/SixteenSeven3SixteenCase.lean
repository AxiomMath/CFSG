module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResults2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3SixteenOrd
public import CFSG.Open.GeneralizedFittingSelfCentralizing
public import CFSG.ClassicalInvolution.Q3.Q3TLTShapeAb
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.GH74.GLS.Stage2.Final.ModelOrd
public import CFSG.LieType.CurtisTits.SpecialLinear
public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCaseTwoCMSection
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatAlt
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusPiecesEmbed
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotLeviFactPiece
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165ExclCard
public import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusExtraction

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16c167_card_Mbar_le_of_case168_8 (D : Data G) {V₀ V : Subgroup G}
    (hV : IsElemAbelian 2 V) (h8 : Case168_8 D V₀ V hV) :
    Nat.card ↥(Mbar D.M V₀ V hV) ≤ 432 := by
  classical
  haveI : Finite (MulAut (Vtil V₀ V hV)) := MulEquiv.finite_left
  let Mb : Subgroup (MulAut (Vtil V₀ V hV)) := Mbar D.M V₀ V hV
  let F₀ : Subgroup ↥Mb := genFittingFStar ↥Mb
  haveI : Finite ↥Mb := Subtype.finite
  have hnorm : F₀.Normal := CFSG.ClassicalInvolution.Q3.genFittingFStar_isNormal
  have hself : centralizer (F₀ : Set ↥Mb) ≤ F₀ :=
    CFSG.Open.Open.generalized_fitting_self_centralizing ↥Mb
  obtain ⟨e'⟩ := h8.1
  let e₀ : ↥F₀ ≃* Multiplicative (Fin 2 → ZMod 3) :=
    (Subgroup.equivMapOfInjective F₀ Mb.subtype Mb.subtype_injective).trans e'
  exact s16c167_card_le_of_isElemAbelianOfRank_three_two hself ⟨e₀⟩

theorem s16c167_card_lBar_le_of_case168_8 (D : Data G) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hLM : L ≤ D.M) (h8 : Case168_8 D V₀ V hV) :
    Nat.card ↥(lBar V₀ V hV L) ≤ 432 := by
  haveI : Finite (MulAut (Vtil V₀ V hV)) := MulEquiv.finite_left
  exact (Subgroup.card_le_of_le (barSub_mono V₀ V hV hLM)).trans
    (s16c167_card_Mbar_le_of_case168_8 D hV h8)

theorem s16c167_case_ln_four (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : Counterex16 D V₀ V L hV) (hL : IsLn ↥(lBar V₀ V hV L) 4 1)
    (h : Concl1613_2 D V₀ V hV L) :
    Case168_2Shape D V₀ V hV L (Shape168_2Ln V₀ V hV L 4) := by
  have hN : Nat.card ↥(lBar V₀ V hV L) = 20160 := s16c167_card_isLn_four hL
  rcases h with h | ⟨p, hp, h⟩ | h | h | h | ⟨p, hp, h⟩ | h
  · obtain ⟨h1, ⟨L₀, hI, hS⟩, h3⟩ := h
    rcases hS with hS | hS | hS | hS
    · have := s16c167_card_isAlt_six hS.2.1
      omega
    · have := s16c167_card_isAlt_seven hS.2.1
      omega
    · exact ⟨h1, ⟨L₀, hI, hS⟩, h3⟩
    · have := s16c167_card_isOmegaMinus_six hS.2.1
      omega
  · rcases hp with rfl | rfl
    · have h3 := s16c167_card_isElemAbelianOfRank h.1
      omega
    · have h3 := s16c167_card_isElemAbelianOfRank h.1
      omega
  · have h3 := h.1.2.1
    omega
  · have := s16c167_card_lBar_le_of_case168_8 D hc.setting.hyp151.le h
    omega
  · have := Om8Excl.card_isL3_one h.2.1
    omega
  · have h3 := h.1.2
    rcases hp with rfl | rfl <;> omega
  · have h3 := h.1.2
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
