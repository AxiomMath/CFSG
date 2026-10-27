module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165Bar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165SevenA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165SevenB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenTI
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs15
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22e
public import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge4
public import CFSG.LocalAnalysis.UniquenessCase.UC6R2
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
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusPiecesOrders
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotLeviFactPiece
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16c
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165ExclDirect
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Norm
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusExtraction

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_mem_normalizer_subgroupOf {M T : Subgroup G} (hTM : T ≤ M) {y : ↥M}
    (hy : y ∈ normalizer ((T.subgroupOf M : Subgroup ↥M) : Set ↥M)) :
    (y : G) ∈ normalizer (T : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  by_cases hhM : h ∈ M
  · have h1 := Subgroup.mem_normalizer_iff.1 hy ⟨h, hhM⟩
    simpa [Subgroup.mem_subgroupOf] using h1
  · constructor
    · intro hT
      exact absurd (hTM hT) hhM
    · intro hT
      have h2 : (y : G) * h * (y : G)⁻¹ ∈ M := hTM hT
      have h3 : (y : G)⁻¹ * ((y : G) * h * (y : G)⁻¹) * (y : G) ∈ M :=
        M.mul_mem (M.mul_mem (M.inv_mem y.2) h2) y.2
      have h4 : (y : G)⁻¹ * ((y : G) * h * (y : G)⁻¹) * (y : G) = h := by group
      rw [h4] at h3
      exact absurd h3 hhM

theorem false_of_noncyclic_seven_normalizer (D : Data G) (h61 : UC6.R6_1 D)
    (h640 : UC6.R6_40_2 D) (h7 : 7 ∈ D.sig) {Y : Subgroup ↥D.M}
    (hYN : Y ≤ normalizer ((D.T.subgroupOf D.M : Subgroup ↥D.M) : Set ↥D.M))
    (hYp : IsPGroup 7 Y) (hYc : ¬ IsCyclic Y) : False := by
  have hTM : D.T ≤ D.M := D.sylowM.le
  have hXM : Y.map D.M.subtype ≤ D.M := Subgroup.map_subtype_le Y
  have hXp : IsPGroup 7 (Y.map D.M.subtype) := hYp.map D.M.subtype
  have hXc : ¬ IsCyclic (Y.map D.M.subtype) := fun hcyc =>
    hYc ((MulEquiv.isCyclic
      (Subgroup.equivMapOfInjective Y D.M.subtype D.M.subtype_injective)).2 hcyc)
  have hXN : Y.map D.M.subtype ≤ normalizer (D.T : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    exact mem_normalizer_of_mem_normalizer_subgroupOf hTM (hYN hy)
  have hle : UC6.calCGS D.T ≤ D.M := uc22p22e_calCGS_le D h61 h7 hXM hXp hXc hXN le_rfl
  rw [h640.1] at hle
  exact uc22br4_M_ne_top D (top_le_iff.1 hle)

theorem false_of_seven_not_pow_three_dvd (D : Data G) (h61 : UC6.R6_1 D) (h129 : R129_1 D)
    {V₀ V : Subgroup G} (hH : Hyp125 D V₀ V) (hV : IsElemAbelian 2 V) (hc4 : Nat.card V₀ ≤ 4)
    (h7 : 7 ∈ D.sig) (hMst : D.M ≤ stabTil V₀ V) (S : OmegaModel (Vtil V₀ V hV))
    (hK : Nat.card S.K = 8) (hΩr : S.omega ≤ (barHom V₀ V hV hMst).range)
    {E : Subgroup ↥D.M} (hE : IsElemAbelian 7 E) (hEc : 7 ^ 3 ≤ Nat.card E)
    (hker : ∀ E' : Subgroup ↥D.M, IsElemAbelian 7 E' → E' ≤ (barHom V₀ V hV hMst).ker →
      Nat.card E' ≤ 7)
    (hrange : ¬ 7 ^ 3 ∣ Nat.card (barHom V₀ V hV hMst).range) : False := by
  have hMn : D.M ≤ normalizer (V : Set G) := hH.pairFacts.le_normalizer
  refine h129 V₀ V hH (s16_TI_of_pRank D h61 hV hMn fun w hw hw1 => ?_)
  refine ⟨7, h7, ?_⟩
  obtain ⟨E', hE', hE'c, hfix⟩ : ∃ E' : Subgroup ↥D.M, IsElemAbelian 7 E' ∧ 7 ^ 2 ≤ Nat.card E' ∧
      ∀ y ∈ E', barHom V₀ V hV hMst y (mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩)) =
        mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩) := by
    by_cases h1 : mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩) = 1
    · refine ⟨E, hE, ?_, fun y _ => ?_⟩
      · exact le_trans (by norm_num) hEc
      · rw [h1, map_one]
    · exact S.exists_isElemAbelian_fix_of_ne_one hK (barHom V₀ V hV hMst) hΩr hE hEc hker hrange h1
  have hcomm : ∀ y ∈ E', (y : G) * w * (y : G)⁻¹ * w⁻¹ ∈ V₀ := fun y hy =>
    (barHom_fix_iff V₀ V hV hMst y (IntMod.mk hV ⟨w, hw⟩)).1 (hfix y hy)
  have hPp : IsPGroup 7 (E'.map D.M.subtype) := hE'.isPGroup.map D.M.subtype
  have hlt : Nat.card V₀ < 7 := by omega
  have hPc : E'.map D.M.subtype ≤ centralizer ({w} : Set G) := by
    refine Om8Lift.le_centralizer_of_conj_mem Nat.prime_seven hPp hlt fun z hz => ?_
    obtain ⟨y, hy, rfl⟩ := hz
    exact hcomm y hy
  refine Om8Lift.two_le_pRank_of_card Nat.prime_seven (E := E'.map D.M.subtype)
    (le_inf (Subgroup.map_subtype_le E') hPc) (hE'.map D.M.subtype) ?_
  rw [Subgroup.card_map_of_injective D.M.subtype_injective]
  exact hE'c

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
