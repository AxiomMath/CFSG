module

public import CFSG.LocalAnalysis.StandardType.GGQTwoCavImage
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.StandardType.QTwoCav

open CFSG.Assembly


variable {G : Type} [Group G] {p : ℕ} {Bs L : Subgroup G}

theorem innerDiagOnLabel_of_marking {lab : LargeEvenLabel}
    (hI : GGInnerDiagOn Bs L) (hM : LargeEvenMarking L (fun lab' _ _ _ _ _ => lab' = lab)) :
    GGInnerDiagOnLabel (fun _ lab' => lab' = lab) p Bs L := by
  obtain ⟨hL, lab', hlab', hraw⟩ := hM
  have hEq : lab' = lab := by
    obtain ⟨_, _, _, _, _, _, _, h⟩ := largeEvenRawDatum_exists hraw
    exact h
  subst lab'
  have hhas : GGHasLabel lab (L ⧸ Subgroup.center L) := by
    unfold GGHasLabel
    exact largeEvenRawDatum_mono (fun _ _ _ _ ⟨_, _, θ, _⟩ => ⟨θ⟩) hraw
  exact ggInnerDiagOn_relabel ggLabelRigidInput_holds hI hlab' hhas

theorem innerDiagOnLabel_of_setting [Finite G] {B D J : Subgroup G} {x : G}
    (hS : GGQTwoSetting p B Bs x L D J) {lab : LargeEvenLabel}
    (hM : LargeEvenMarking L (fun lab' _ _ _ _ _ => lab' = lab)) :
    GGInnerDiagOnLabel (fun _ lab' => lab' = lab) p Bs L := by
  exact innerDiagOnLabel_of_marking hS.1.2.2.1.1 hM

end CFSG.StandardType.QTwoCav

end
