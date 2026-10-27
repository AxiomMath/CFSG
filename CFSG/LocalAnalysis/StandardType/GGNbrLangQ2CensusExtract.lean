module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusDefs
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly


theorem q2c_extract {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) (hInner : GGInnerDiagOn Bs L) :
    ∃ lab : LargeEvenLabel, GGInnerDiagOnLab (fun _ lab' => lab' = lab) p Bs L := by
  have hst : LargeEvenStandardType p B x L := hcfg.1.2.2.2.2.2.2.2
  obtain ⟨hperf, lab, hΛ, hraw⟩ := hst.1
  have hhas : GGHasLabel lab (↥L ⧸ Subgroup.center ↥L) := by
    unfold GGHasLabel
    refine largeEvenRawDatum_mono (fun R _ I F hh => ?_) hraw
    obtain ⟨-, -, θ, -⟩ := hh
    exact ⟨θ⟩
  have hsplit : LargeEvenSplit p lab := by
    obtain ⟨R, _, I, F, -, -, θ, hP⟩ := largeEvenRawDatum_exists hraw
    exact hP.1
  have hrelab := ggInnerDiagOn_relabel ggLabelRigidInput_holds hInner hΛ hhas
  refine ⟨lab, largeEvenMarking_mono ?_ hrelab⟩
  rintro lab' R _ I F θ ⟨hl, hN, hb⟩
  exact ⟨hl, hl ▸ hsplit, hN, hb⟩

end CFSG.StandardType
