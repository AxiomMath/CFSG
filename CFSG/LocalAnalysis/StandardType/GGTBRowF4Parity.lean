module

public import CFSG.LocalAnalysis.StandardType.GGTBRowDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwenty
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGTableBF4
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGRootGenExcLabels

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggInnerDiagOnLabel_f4Split_of_rowR4 (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hHyp : GGCorFiveTwentyHyp p B Bs x L D J)
    (hL : GGInnerDiagOnLabel (fun p lab => GGLabQFour p lab ∧ GGTBRowR4 p lab) p Bs L) :
    GGInnerDiagOnLabel GGTableBF4Label p Bs L := by
  have hst : LargeEvenStandardType p B x L := hHyp.1.1.2.2.2.2.2.2.2
  obtain ⟨labs, hlabs, hhass, _, _, _, _, _, hPs⟩ := largeEvenMarking_exists_hasLabel hst.1
  obtain ⟨lab1, hlab1, hhas1, _, _, _, _, _, hP1⟩ := largeEvenMarking_exists_hasLabel hL
  obtain ⟨hQ4, hrow⟩ := hP1.1
  unfold GGLabQFour at hQ4
  unfold GGTBRowR4 at hrow
  have heq : labs = lab1 :=
    eq_of_ggLabelIso_of_excTag (Or.inr (Or.inr (Or.inr (Or.inl hrow))))
      (hRig lab1 labs _ hlab1 hlabs hhas1 hhass)
  have hs : LargeEvenSplit p lab1 := by
    have h := hPs.1
    rwa [heq] at h
  have hbad : GGTableBF4Label p lab1 := by
    refine ⟨hrow, ?_⟩
    rcases (largeEvenSplit_F4_iff hrow).mp hs with hdvd | ⟨hn1, -⟩
    · exact hdvd
    · exfalso
      rw [hn1] at hQ4
      omega
  have hmark := ggInnerDiagOn_relabel hRig hHyp.2.2.1.1 hlab1 hhas1
  refine largeEvenMarking_mono ?_ hmark
  intro lab' _ _ _ _ _ hP'
  obtain ⟨hlab', hBN, hBI⟩ := hP'
  exact ⟨by rw [hlab']; exact hbad, hBN, hBI⟩

end CFSG.StandardType

end
