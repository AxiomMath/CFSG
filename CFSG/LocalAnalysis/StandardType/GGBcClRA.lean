module

public import CFSG.LocalAnalysis.StandardType.GGBcDefs
public import CFSG.LocalAnalysis.StandardType.GGTPNThmRACore
public import CFSG.LocalAnalysis.StandardType.GGTPNThmRAC1
public import CFSG.LocalAnalysis.StandardType.GGTPNThmRADescent
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem bcra_tag_ne_aux {t : LargeEvenLieTag}
    (hY : t = .A ∨ t = .twA) (hBC : t = .B ∨ t = .C) : False := by
  rcases hY with h | h <;> rcases hBC with h' | h' <;> rw [h] at h' <;> cases h'

private theorem bcra_not_bc_of_tag {t : LargeEvenLieTag}
    (ht : t = .A ∨ t = .twA ∨ t = .D ∨ t = .twD) (hBC : t = .B ∨ t = .C) : False := by
  rcases ht with h | h | h | h <;> rcases hBC with h' | h' <;> rw [h] at h' <;> cases h'

private theorem bcra_tag_ne_bc_of_ggLabelIso (lab labY : LargeEvenLabel)
    (hY : labY.tag = .A ∨ labY.tag = .twA) (hBC : lab.tag = .B ∨ lab.tag = .C)
    (hiso : GGLabelIso lab labY) : False := by
  unfold GGLabelIso at hiso
  rcases hiso with h | h | h | h | h | h | h | h
  · exact bcra_tag_ne_aux (t := lab.tag) (by rw [h]; exact hY) hBC
  · exact bcra_tag_ne_aux hY h.2.1
  · exact bcra_not_bc_of_tag (Or.inr (Or.inr (Or.inl (congrArg LargeEvenLabel.tag h.1)))) hBC
  · exact bcra_not_bc_of_tag (Or.inl (congrArg LargeEvenLabel.tag h.1)) hBC
  · exact bcra_not_bc_of_tag (Or.inr (Or.inr (Or.inr (congrArg LargeEvenLabel.tag h.1)))) hBC
  · exact bcra_not_bc_of_tag (Or.inr (Or.inl (congrArg LargeEvenLabel.tag h.1))) hBC
  · exact bcra_not_bc_of_tag (Or.inr (Or.inr (Or.inr (congrArg LargeEvenLabel.tag h.1)))) hBC
  · exact bcra_not_bc_of_tag (Or.inl (congrArg LargeEvenLabel.tag h.2)) hBC

private theorem bcra_not_ggHasLabel_bc_of_ggKacRA (hrig : GGLabelRigidInput) {p : ℕ}
    (hp : p.Prime) {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)} {σ : MulAut X}
    {J : Subgroup X} (hloc : GGTPNLocalCore p A σ J) (h8 : GGTPNOnlyComp p σ J)
    (hm : GGTPNMarked p (fun _ _ => True) A) {labX : LargeEvenLabel}
    (hΛX : LargeEvenInLambda2 labX) (hRA : GGKacRA labX p)
    (hhX : GGHasLabel labX (X ⧸ Subgroup.center X)) {labJ : LargeEvenLabel}
    (hΛJ : LargeEvenInLambda2 labJ) (hBC : labJ.tag = .B ∨ labJ.tag = .C)
    (hhJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J)) : False := by
  have hm' : GGTPNMarked p (fun _ lab => lab = labX) A :=
    ggTPNMarked_eq_of_ggKacRA hrig hp hm hΛX hRA hhX
  have htagX : labX.tag = .A ∨ labX.tag = .twA := by
    rcases hRA with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  rcases split_or_fieldType_of_ggKacRA hp hloc h8 hRA hm' with
    ⟨a, ds, -, -, -, -, hcase⟩ | ⟨-, -, hcase⟩
  · rcases hcase with ⟨hΛY, hY⟩ | ⟨-, -, hΛY, hY⟩
    · exact bcra_tag_ne_bc_of_ggLabelIso labJ ⟨labX.tag, a - 1, labX.n⟩
        (by simpa using htagX) hBC
        (hrig labJ ⟨labX.tag, a - 1, labX.n⟩ _ hΛJ hΛY hhJ hY)
    · exact bcra_tag_ne_bc_of_ggLabelIso labJ ⟨.A, 1, labX.n⟩ (Or.inl rfl) hBC
        (hrig labJ ⟨.A, 1, labX.n⟩ _ hΛJ hΛY hhJ hY)
  · rcases hcase with ⟨-, hΛY, hY⟩ | ⟨-, -, hΛY, hY⟩
    · exact bcra_tag_ne_bc_of_ggLabelIso labJ ⟨.A, (labX.rank + 1) / p - 1, p * labX.n⟩
        (Or.inl rfl) hBC
        (hrig labJ ⟨.A, (labX.rank + 1) / p - 1, p * labX.n⟩ _ hΛJ hΛY hhJ hY)
    · exact bcra_tag_ne_bc_of_ggLabelIso labJ ⟨.twA, (labX.rank + 1) / p - 1, p * labX.n⟩
        (Or.inr rfl) hBC
        (hrig labJ ⟨.twA, (labX.rank + 1) / p - 1, p * labX.n⟩ _ hΛJ hΛY hhJ hY)

theorem ggBcClRARK_holds :
    GGBcClRARK := by
  intro p hp hp2 X _ _ A Ab σ J n hd _ labJ labX hΛJ hΛX hr hhJ hhX
  have hrig : GGLabelRigidInput := ggLabelRigidInput_holds
  obtain ⟨⟨hloc, -, -, -, -, -, h8, hm⟩, -⟩ := hd
  exact (bcra_not_ggHasLabel_bc_of_ggKacRA hrig hp hloc h8 hm hΛX hr.2 hhX hΛJ hr.1.1 hhJ).elim

end CFSG.StandardType

end
