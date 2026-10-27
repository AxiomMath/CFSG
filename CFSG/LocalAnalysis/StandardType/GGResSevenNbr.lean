module

public import CFSG.LocalAnalysis.StandardType.GGResLeaves
public import CFSG.LocalAnalysis.StandardType.GGNbrLabelJOfTcjK
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGTPNNarrow
public import CFSG.LocalAnalysis.StandardType.GGForkA8NotRefl
public import CFSG.LocalAnalysis.StandardType.GGForkA8TablePOn
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyNbrFieldRows
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyNbrFieldRowsNarrow
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflDom
public import CFSG.LocalAnalysis.StandardType.GGNbrHalfSplitArith
public import CFSG.LocalAnalysis.StandardType.GGRootGenExcLabels
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplit

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGSevenLabel (X : LargeEvenLabel) : Prop :=
  X = ⟨.A, 8, 1⟩ ∨ X = ⟨.A, 11, 1⟩ ∨ X = ⟨.E6, 0, 1⟩ ∨ X = ⟨.twE6, 0, 1⟩ ∨ X = ⟨.E8, 0, 1⟩

private theorem l48f_eq_of_iso_seven {lab labX : LargeEvenLabel}
    (hiso : GGLabelIso lab labX) (hX : GGSevenLabel labX) : lab = labX := by
  rcases hX with rfl | rfl | rfl | rfl | rfl <;>
    (rcases hiso with rfl | h | h | h | h | h | h | h <;>
      first
        | rfl
        | (exfalso; simp_all))

private theorem l48f_ne_of_tag_ne {lab lab' : LargeEvenLabel} (h : lab.tag ≠ lab'.tag) :
    lab ≠ lab' := fun he => h (congrArg LargeEvenLabel.tag he)

private theorem l48f_ne_of_rank_ne {lab lab' : LargeEvenLabel} (h : lab.rank ≠ lab'.rank) :
    lab ≠ lab' := fun he => h (congrArg LargeEvenLabel.rank he)

private theorem l48f_halfSplit_absurd
    {G : Type} [Group G] [Finite G] (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hRig : GGLabelRigidInput) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} {labX : LargeEvenLabel}
    (hcfg : GGConfig 7 B Bs x L D J) (hinn : GGInnerDiagAll 7 B Bs x L D J)
    (hnb : GGNbr 7 B x D J y K) (hΛ : LargeEvenInLambda2 labX)
    (hX : GGHasLabel labX (↥K ⧸ Subgroup.center ↥K)) (hX1 : labX.n = 1)
    (hnoalias : ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
      GGHasLabel lab (↥K ⧸ Subgroup.center ↥K) → GGLabelIso lab labX → lab = labX)
    (hne : labX ≠ ⟨.A, 8, 1⟩ ∧ labX ≠ ⟨.E6, 0, 1⟩) : False := by
  have hHS := ggNbr_halfSplit_of_hyp hraw hiso hcfg hnb (hinn.2 y K hnb)
  obtain ⟨lab, hlab, hhas, R, _, I, F, θ, hHSlab⟩ := largeEvenMarking_exists_hasLabel hHS
  have hisoLab : GGLabelIso lab labX := hRig lab labX _ hlab hΛ hhas hX
  have heq : lab = labX := hnoalias lab hlab hhas hisoLab
  rcases largeEvenHalfSplit_dvd hlab hHSlab with hd | ⟨-, hex⟩
  · rw [heq, hX1] at hd
    norm_num at hd
  · rw [heq] at hex
    rcases hex with h | h
    · exact hne.1 h
    · exact hne.2 h

theorem ggSeven_L_absurd
    {G : Type} [Group G] [Finite G] (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput) {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hp : p = 7) {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K) {labX : LargeEvenLabel}
    (hΛ : LargeEvenInLambda2 labX) (hX : GGHasLabel labX (↥L ⧸ Subgroup.center ↥L))
    (h5 : GGSevenLabel labX) : False := by
  subst hp
  obtain ⟨lab, labJ, hlab, hsplit, hhas, -, -, -⟩ := ggNbr_label_J_of_tcj hTCJ hcfg hnb
  have hiso : GGLabelIso lab labX := hRig lab labX _ hlab hΛ hhas hX
  have hlabX : lab = labX := l48f_eq_of_iso_seven hiso h5
  rw [hlabX] at hsplit
  have h1 : labX.n = 1 := by rcases h5 with rfl | rfl | rfl | rfl | rfl <;> rfl
  have h3 : 3 ∣ labX.n := largeEvenSplit_seven_dvd hsplit
  rw [h1] at h3
  norm_num at h3

theorem ggSeven_K_absurd
    {G : Type} [Group G] [Finite G] (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput) {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hp : p = 7) {labX : LargeEvenLabel}
    (hΛ : LargeEvenInLambda2 labX) (hX : GGHasLabel labX (↥K ⧸ Subgroup.center ↥K))
    (h5 : GGSevenLabel labX) : False := by
  obtain ⟨hcfg, hOp, hinn, hNoTr, hnb, hRG, -⟩ := hH
  subst hp
  rcases h5 with rfl | rfl | rfl | rfl | rfl
  · exact ggForkNbrSevenExcl'_of_notRefl hA8 G B Bs x L D J hcfg hOp hinn hNoTr y K hnb hRG hX
  · refine l48f_halfSplit_absurd hraw hiso hRig hcfg hinn hnb hΛ hX rfl ?_ ⟨?_, ?_⟩
    · intro lab hlab hhas hisoLab
      exact l48f_eq_of_iso_seven hisoLab (Or.inr (Or.inl rfl))
    · intro h
      exact l48f_ne_of_rank_ne (by norm_num) h
    · intro h
      exact l48f_ne_of_tag_ne (by simp) h
  · exact ggForkA8_not_e6Nbr hTPn.toFieldTwo hTCJ hRig hcfg hinn hnb hX
  · refine l48f_halfSplit_absurd hraw hiso hRig hcfg hinn hnb hΛ hX rfl ?_ ⟨?_, ?_⟩
    · intro lab hlab hhas hisoLab
      exact eq_of_ggLabelIso_of_twE6 rfl hisoLab
    · intro h
      exact l48f_ne_of_tag_ne (by simp) h
    · intro h
      exact l48f_ne_of_tag_ne (by simp) h
  · refine l48f_halfSplit_absurd hraw hiso hRig hcfg hinn hnb hΛ hX rfl ?_ ⟨?_, ?_⟩
    · intro lab hlab hhas _
      exact eq_of_ggLabelIso_of_excTag (lab := ⟨.E8, 0, 1⟩) (lab' := lab)
        (Or.inr (Or.inr (Or.inl rfl))) (hRig ⟨.E8, 0, 1⟩ lab _ hΛ hlab hX hhas)
    · intro h
      exact l48f_ne_of_tag_ne (by simp) h
    · intro h
      exact l48f_ne_of_tag_ne (by simp) h

end CFSG.StandardType

end
