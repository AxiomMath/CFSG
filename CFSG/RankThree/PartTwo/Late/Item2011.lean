module

import CFSG.RankThree.PartTwo.Sec13.OmegaNonempty
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartTwo.Sec13.Item13Inputs
public import CFSG.RankThree.PartTwo.Sec17.Item1729
public import CFSG.RankThree.PartTwo.Sec18.Notation
import CFSG.RankThree.PartTwo.Sec19.Step1911EndKFact
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec18 CFSG.RankThree.PartTwo.Sec19

theorem item13Setup_of (hsetAt : Item13SetupAt) : Sec17.Item13Setup := by
  intro G _ _ hG hS A hAF hAT
  obtain ⟨F, hF⟩ := omegaA_nonempty hG hS hAF hAT
  obtain ⟨-, -, a, rfl, -⟩ := id hF
  obtain ⟨L, hL⟩ := hsetAt G hG hS A hAF hAT a hF
  exact ⟨a, L, hF, hL⟩

end CFSG.RankThree.PartTwo.Late
