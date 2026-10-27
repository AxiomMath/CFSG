module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R856Normal
public import CFSG.LocalAnalysis.UniquenessCase.UC22R856NormalCoverFacts
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight56U14Covers
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.Three
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36SporGe4
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36ODCCent
public import CFSG.LocalAnalysis.UniquenessCase.UC6K316Out
public import CFSG.LieType.SeitzGeneration.SeitzStatus
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36SporPairs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.PartOneSixNine
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight62OneControl
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight5xA859

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three

open Subgroup CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

variable {G : Type} [Group G] [Finite G]

theorem r862_dataOfSetup
    (hS : Standing G) (hUC : CFSG.Open.rankThreeUC G) (hC : AGL81TheoremC G) (S : Setup G) :
    R862 (dataOfSetup hS S) := by
  have hSg := UC6S846.sigmaStd_dataOfSetup hS S
  have h614 := UC6G.uc_theorem_6_14_three hS hUC hC (UCK.k36_of_eqlStar
      (UCK.k36EqlStar_of_catalog CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds
          UCK.k36OddDefChar_holds UCK.k315Spor_holds UCK.k36EqlStarSporGe4_holds) UCK.l34OuterFree) S
  have h857 := R856Normal.r857_of_data hSg h614
  have h859 := r859_of_r858 (r858_of_r857 hSg h857)
  have h860 := r860_of_inputs hSg h614 h859 (fun L Q P hc => (h857 L Q P hc).2.1)
  have h63 := r6_3_dataOfSetup hS hUC hC S
  intro L' Q' P' hc
  have hPL : P' ≤ normalizer (L' : Set G) := h859 L' Q' P' hc
  have h61 : ∀ A : Subgroup G, A ≤ P' → Nat.card A = 3 → ¬ A ≤ Q' →
      2 ≤ CFSG.Open.pRank 3 (centralizer (A : Set G) ⊓ L') := by
    intro A hAP hAc hAQ
    exact h61_of_list857
      CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.outerFixedE9_holds
      hc.mem hc.rank (h857 L' Q' P' hc).1 (h860 L' Q' P' hc)
      hc.sylowQ hc.sylowP hc.le hPL A hAP hAc hAQ
  refine ⟨?_, ?_⟩
  · intro A hAP g hg
    exact exists_mem_conj_forall_of_centralizer_transport h63 hc.mem.1.le hc.sylowQ
      hc.le hc.sylowP hc.rank.ge hc.gamma hPL h61 hAP hg
  · intro A hAP hN
    have hA := inU_of_normalizer_le_of_centralizer_transport h63 hc.mem.1.le hc.sylowQ
      hc.le hc.sylowP hc.rank.ge hc.gamma hPL h61 hAP hN
    refine ⟨hA.1, ?_⟩
    intro k hk
    have hk' : A ≤ CFSG.Open.uniqueFourConj k⁻¹ (dataOfSetup hS S).M := by
      simpa [CFSG.Open.uniqueFourConj] using hk
    have hconj := hA.2 k⁻¹ hk'
    simpa [CFSG.Open.uniqueFourConj, dataOfSetup] using hconj

theorem false_of_normal_triple_cover_dataOfSetup
    (hS : Standing G) (hUC : CFSG.Open.rankThreeUC G) (hC : AGL81TheoremC G) (S : Setup G)
    {L Q P X : Subgroup G} (h : ChoiceX (dataOfSetup hS S) L Q P X)
    (hLM : S.M ≤ normalizer (L : Set G)) (hcov : List857Clause2 (Bar2 L)) : False := by
  have hSg := UC6S846.sigmaStd_dataOfSetup hS S
  have h614 := UC6G.uc_theorem_6_14_three hS hUC hC (UCK.k36_of_eqlStar
      (UCK.k36EqlStar_of_catalog CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds
          UCK.k36OddDefChar_holds UCK.k315Spor_holds UCK.k36EqlStarSporGe4_holds) UCK.l34OuterFree) S
  have h857 := R856Normal.r857_of_data hSg h614
  have h859 := r859_of_r858 (r858_of_r857 hSg h857)
  have h63 := r6_3_dataOfSetup hS hUC hC S
  have hc := h.cex
  have hPL : P ≤ normalizer (L : Set G) := hc.sylowP.le.trans hLM
  have h61 := h61_of_list857Clause2 (Q := Q) hc.mem hc.rank hcov hPL
  have hE := hasGammaE9_of_pRank hc (h61 X h.le h.card h.not_le_sylowQ)
  have hU : ∀ A : Subgroup G, A ≤ P → normalizer (A : Set G) ≤ (dataOfSetup hS S).M →
      A ∈ uniqueSet (dataOfSetup hS S).M := by
    intro A hAP hN
    have hA := inU_of_normalizer_le_of_centralizer_transport h63 hc.mem.1.le hc.sylowQ
      hc.le hc.sylowP hc.rank.ge hc.gamma hPL h61 hAP hN
    refine ⟨hA.1, ?_⟩
    intro k hk
    have hk' : A ≤ CFSG.Open.uniqueFourConj k⁻¹ (dataOfSetup hS S).M := by
      simpa [CFSG.Open.uniqueFourConj] using hk
    have hconj := hA.2 k⁻¹ hk'
    simpa [CFSG.Open.uniqueFourConj, dataOfSetup] using hconj
  have hN : ¬ normalizer (X : Set G) ≤ S.M := fun hn =>
    h.notLe ((centralizer_le_normalizer _).trans hn)
  have h69 := r6_9_dataOfSetup hS hUC hC (UCK.k36_of_eqlStar
      (UCK.k36EqlStar_of_catalog CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds
          UCK.k36OddDefChar_holds UCK.k315Spor_holds UCK.k36EqlStarSporGe4_holds) UCK.l34OuterFree) S
  have hXL : ⁅L, X⁆ ≤ pCoreOf 2 L := by
    rw [Subgroup.commutator_comm]
    exact r861_cover_of_spine hSg h69 h857 h859 L Q P hc X h.le h.card h.not_le_sylowQ hN hE hcov
  obtain ⟨LX, hG⟩ := coverCoreG_of_choiceX_of_uniqueSet (dataOfSetup hS S)
    hSg h69 h857 h859 hXL h hcov hLM hU
  exact false_of_coverCore_of_rows (coverCore_of_coverCoreG hG)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three
