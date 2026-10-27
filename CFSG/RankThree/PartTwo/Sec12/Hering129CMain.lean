module

public import CFSG.RankThree.PartTwo.Sec12.Hering129CRed3
public import CFSG.RankThree.PartTwo.Sec12.Hering129LOTwo
import CFSG.RankThree.PartTwo.Sec12.Gap128OTwoHJ

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open Hering129C


theorem gap127TwoCfg_of_census (h1 : Sec4.Item4_1LargePrime) (h46 : Sec4.Item4_6)
    (h125 : Item125BarC9) (hOTwo : KS129OTwoLie) (hC : KFCensus) : Gap127TwoCfg := by
  intro G _ _ A c L b a K S cfg
  have hG := cfg.std.toTheoremFourHyp
  obtain ⟨-, -, -, hb1, -⟩ := cfg.point_facts
  have hKperf : Group.IsPerfect ↥K := Sec6.isPerfect_of_mem_thetaComponentsAt cfg.hK
  have hKne : K ≠ ⊤ := fun h =>
    Sec6.centralizer_ne_top_of_ne_one hG hb1
      (top_le_iff.mp (h ▸ K_le_centralizer_b cfg))
  have hS4K : SectionFourHyp ↥K := hG.sectionFourHyp hKne
  have hconcl := hC (↥K ⧸ aschbacherSolvableCore 3 ↥K) (L ⧸ aschbacherSolvableCore 3 L)
    (barK K c (c_mem_K cfg)) (barK K a (a_mem_K cfg)) (Ibar L K b (hIK_cfg cfg)) (Xbar A K)
    (fCfg cfg) (isList46_of_cfg h46 cfg) (census129_of_cfg h1 h125 cfg)
  rcases hconcl with ⟨⟨e⟩, hL⟩ | ⟨q, hq, hQ⟩
  · exact Or.inl ⟨hL, gap128OTwoHJ ↥K hS4K hKperf ⟨e⟩⟩
  · refine Or.inr ⟨q, hq, ?_⟩
    rcases hQ with hG2 | ⟨hv, ⟨e⟩⟩
    · have hθ := hOTwo ↥K hS4K hKperf (Or.inl ⟨q, hG2⟩)
      obtain ⟨hv, ⟨e⟩⟩ := hG2
      exact Or.inl ⟨hv, ⟨(QuotientGroup.quotientMulEquivOfEq hθ).symm.trans e⟩⟩
    · have hθ := hOTwo ↥K hS4K hKperf (Or.inr ⟨q, hv, ⟨e⟩⟩)
      exact Or.inr ⟨hv, ⟨(QuotientGroup.quotientMulEquivOfEq hθ).symm.trans e⟩⟩

end CFSG.RankThree.PartTwo.Sec12
