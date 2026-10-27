module

public import CFSG.RankThree.PartTwo.Sec19.LitScopeProof
public import CFSG.RankThree.PartTwo.Sec19.Item19Res5ProofStep202J
public import CFSG.RankThree.PartTwo.Sec20.Item20Res5ProofSteps
public import CFSG.RankThree.PartTwo.Sec20.Item20Res6ProofJ

public section

namespace CFSG.RankThree.PartTwo.Sec19.Item19Res5Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec20
open CFSG.AGLEmbedding (Asc81bEightFour)

theorem step202J_of_census194Wide_rank
    (h84 : Asc81bEightFour) (h93 : Asc81bNineThreeRank) (h316 : Item316)
    (hC : Census194Wide) : Step202J := by
  intro G _ _ A M L N c h X hX hXM hO2
  have hs : Res6.SettingJ G A M X :=
    { toPartTwoStanding := h.1.toPartTwoStanding
      isE27 := isE27_of_mem_partTwoE h.1.mem_partTwoE
      mem_scriptM := h.1.mem_scriptM
      mem_scriptM_H := ⟨hX.1, fun a ha => hX.2 (Subgroup.mem_sup_left ha)⟩
      ne := hXM
      twoCore_inf := hO2 }
  obtain ⟨K₀, hK₀⟩ := hs.scriptJ_nonempty h84 h316
  refine ⟨K₀, hK₀.1, ?_, hK₀.2⟩
  have hKw := hs.mem_scriptJ_iff.mp hK₀
  have hp : ∀ p : ℕ, p.Prime → 3 < p → CFSG.Open.pRank p M ≤ 2 :=
    fun _ hp hp3 => hs.pRank_le_two hp hp3
  have hc := hC G M (CFSG.Open.pCoreOf 2 X) K₀ hs.isKGroup hs.asc81bHyp hKw
    (h93 G M _ K₀ hs.isKGroup hs.asc81bHyp hKw hp hs.pRank_three_le) (hs.not_isScriptLBlock h316)
    hp hs.pRank_three_le
  exact (three_dvd_card_of_wide hc.1).trans (Subgroup.card_quotient_dvd_card _)

end CFSG.RankThree.PartTwo.Sec19.Item19Res5Proof
