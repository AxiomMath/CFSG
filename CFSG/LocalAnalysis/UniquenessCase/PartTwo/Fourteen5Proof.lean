module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen5
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen5CfgOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen5CfgTwoB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen5Quot2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen5StepD
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen5StepG

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

namespace Cfg145

variable {K : Type} [Group K] [Finite K] {M X₁ X₂ P : Subgroup K}

theorem false (c : Cfg145 M X₁ X₂ P) (hE : K330Cfg.ExclAll) (hKA : KSevenGen)
    (hKB : KThreeInner) :
    False := by
  rcases c.components with ⟨J, hJ, hJu⟩ | ⟨J₁, J₂, hJ₁, hJ₂, hne, hJu⟩
  · exact c.false_of_one_component hE hKB hJ hJu
  · exact c.false_of_two_components hKA hJ₁ hJ₂ hne hJu

end Cfg145

variable {G : Type} [Group G] [Finite G]

theorem thm145 {D : Data G} (hSg : UC6S846.SigmaStd D) (h1421 : Thm1421 D) (h1422 : Thm1422 D)
    (h143 : Thm143 D) (h82 : F08.R82 D) (h63 : UC6.R6_3 D) (h71 : F07.R71 D)
    (hE : K330Cfg.ExclAll) (hKA : KSevenGen) (hKB : KThreeInner) : Thm145 D := by
  intro L₁ L₂ X h H hXH hF hodd hAut h7
  by_cases hs : IsStronglyPEmbedded 3 D.M
  · exact h.le_of_isStronglyPEmbedded hs h63 hXH hF
  have hperm : PermutesPair D.M L₁ L₂ := h.permutesPair h82 hs
  have hL : L₁ ⊔ L₂ = Opp 3 D.M := (h143 L₁ L₂ X h).resolve_left hs
  by_contra hHM
  have hH : H ≠ ⊤ := h.ne_top_of_fstar hXH hF
  have hX3 := h.isSylowOf_three_of_eq_opp h1421 hL hXH
  have hIM := h.primeCore_le hSg h1421 h1422 hperm hXH hF hodd hAut
  have hI7 := not_seven_dvd_card_of_le (h.isStronglyPEmbedded_seven hSg)
    (rankThreePrimeCore_facts H).1 (rankThreePrimeCore_facts H).2.1 hIM hHM
  obtain ⟨P, hP, hPX⟩ := h.exists_isSylowOf_seven_le_centralizer h1422 hperm hH hXH hAut hHM
  have hPc := isCyclic_of_le_of_pRank_le_one hP.le hP.isPGroup
    (h.pRank_seven_le_one hSg h71 hXH hF hHM)
  exact (h.cfg145 hSg h1421 hperm hH hX3 hodd hAut h7 hHM hIM hI7 hP hPX hPc).false hE hKA hKB

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
