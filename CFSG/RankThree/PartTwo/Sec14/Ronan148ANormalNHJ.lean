module

import CFSG.RankThree.PartTwo.Sec14.Item148Proof
import CFSG.RankThree.PartTwo.Sec14.Item148Solvable
public import CFSG.RankThree.PartTwo.Sec14.Item148Steps
import CFSG.CGT.PushingUpLit.Transport
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148A

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.LocalRank CFSG.GH74.GLS

theorem rank3II_14_8_of_cases_local {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G}
    {L : Subgroup G} (h : Sec14Std G A c L)
    (hN : ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
      Ind148 A (lB A) Y → (letI := ker148_normal hY.2; Item148Cases A (lB A) Y) →
      ¬ Case148One A (lB A) Y →
      (((deltaZero A (lB A) Y).subgroupOf Y).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y))).Normal)
    (hcases : ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
      Ind148 A (lB A) Y →
      letI := ker148_normal hY.2
      Item148Cases A (lB A) Y) :
    Item148 A (lB A) := by
  rw [item148_iff]
  suffices key : ∀ n : ℕ, ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), Nat.card Y = n →
      Item148At A (lB A) Y hY from fun Y hY => key _ Y hY rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
    intro Y hY hn
    have ih : Ind148 A (lB A) Y := fun Y' hY' hlt => ihn _ (hn ▸ hlt) Y' hY' rfl
    by_cases hs : Group.IsSolvable ↥Y
    · have h1 : Case148One A (lB A) Y := item148Solvable_of_mem_partTwoF h.mem_partTwoF Y hY hs
      exact And.intro (normal_of_case148One h1) (Or.inl h1)
    have hc := hcases Y hY hs ih
    refine And.intro ?_ hc
    by_cases h1 : Case148One A (lB A) Y
    · exact normal_of_case148One h1
    · exact hN Y hY hs ih hc h1

end CFSG.RankThree.PartTwo.Sec14.Ronan148A
