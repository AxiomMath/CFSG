module

import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec14.Notation
public import CFSG.RankThree.PartTwo.Sec14.Std
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148D

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

theorem mem_of_mem_lbMembers {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c a : G}
    (h : Sec14Std G A c L) {D Lb : Subgroup G} {b d : G} (hD : IsHyperplane A D)
    (hc : IsLBConfig A D b d Lb) (hda : Subgroup.zpowers a = Subgroup.zpowers d)
    {K : Subgroup G} (hDK : lB A D ≤ K) : a ∈ K := by
  have hdA : d ∈ A := hD.1 (hc.1 ▸ Subgroup.subset_closure (Set.mem_insert_of_mem b rfl))
  obtain ⟨hdL, -⟩ := hc.2.2.2.2
  have hdK : d ∈ K :=
    hDK ((Item148HJ.lB_eq_residual h hD hc) ▸ Item148HJ.inf_le_residual h hD hc ⟨hdA, hdL⟩)
  exact Subgroup.zpowers_le.mpr hdK (hda ▸ Subgroup.mem_zpowers a)

end CFSG.RankThree.PartTwo.Sec14.Ronan148D
