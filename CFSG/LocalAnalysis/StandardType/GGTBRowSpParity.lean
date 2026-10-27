module

public import CFSG.LocalAnalysis.StandardType.GGTBRowDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwenty
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflSp
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplectic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggLabelIso_symplectic_tag_n {lab lab' : LargeEvenLabel}
    (ht : lab.tag = .B ∨ lab.tag = .C) (h : GGLabelIso lab lab') :
    (lab'.tag = .B ∨ lab'.tag = .C) ∧ lab'.n = lab.n := by
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨t', r', n'⟩ := lab'
  simp only at ht
  unfold GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h <;> simp_all

theorem ggInnerDiagOnLabel_reflSp_of_rowR3 (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hHyp : GGCorFiveTwentyHyp p B Bs x L D J)
    (hL : GGInnerDiagOnLabel (fun p lab => GGLabQFour p lab ∧ GGTBRowR3 p lab) p Bs L) :
    GGInnerDiagOnLabel GGReflSpLabel p Bs L := by
  have hst : LargeEvenStandardType p B x L := hHyp.1.1.2.2.2.2.2.2.2
  obtain ⟨labs, hlabs, hhass, _, _, _, _, _, hPs⟩ := largeEvenMarking_exists_hasLabel hst.1
  obtain ⟨lab1, hlab1, hhas1, _, _, _, _, _, hP1⟩ := largeEvenMarking_exists_hasLabel hL
  obtain ⟨hQ4, hrow⟩ := hP1.1
  unfold GGLabQFour at hQ4
  unfold GGTBRowR3 at hrow
  have hiso : GGLabelIso lab1 labs := hRig lab1 labs _ hlab1 hlabs hhas1 hhass
  obtain ⟨htag', hn'⟩ := ggLabelIso_symplectic_tag_n hrow.1 hiso
  have hbad : GGReflSpLabel p lab1 := by
    refine ⟨hrow.1, ?_⟩
    rcases (largeEvenSplit_symplectic_iff htag').mp hPs.1 with hdvd | ⟨hn1, -⟩
    · rwa [hn'] at hdvd
    · omega
  have hmark := ggInnerDiagOn_relabel hRig hHyp.2.2.1.1 hlab1 hhas1
  refine largeEvenMarking_mono ?_ hmark
  intro lab' _ _ _ _ _ hP'
  obtain ⟨hlab', hBN, hBI⟩ := hP'
  exact ⟨by rw [hlab']; exact hbad, hBN, hBI⟩

end CFSG.StandardType

end
