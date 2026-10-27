module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInfra
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_CycThreeCent_imgTil_mem_conjSubs
    (D : Data G) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (h : Setting16 D V₀ V L)
    {X : Subgroup G} (hX : X ∈ wConj D.M V₀ V hV L) :
    imgTil V₀ V hV X ∈ conjSubs (Mbar D.M V₀ V hV) (wTil V₀ V hV L) := by
  rw [wConj] at hX
  obtain ⟨m, hm, rfl⟩ := hX
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp16.hyp125.pairFacts.le_normalizer
      h.hyp16.hyp125.pairFacts.le_normalizer₀
  have hmstab : m ∈ stabTil V₀ V := hMs hm
  refine ⟨(actTil V₀ V hV ⟨m, hmstab⟩)⁻¹,
    (Mbar D.M V₀ V hV).inv_mem (actTil_mem_barSub V₀ V hV hm hmstab), ?_⟩
  rw [s15_Infra_imgTil_conjSubgroup V₀ V (wSub V₀ V hV L) hV hmstab, wSub, imgTil_preTil]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
