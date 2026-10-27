module

public import CFSG.LocalAnalysis.StandardType.GGExcRERegimeDefs
public import CFSG.LocalAnalysis.StandardType.GGTPNThmRABase
public import CFSG.LocalAnalysis.StandardType.GGTPNThmUTableClDefs
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGRegimeC2 : ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → Prop :=
  fun p _ labJ _ => labJ.tag = .C ∧ labJ.rank = 2 ∧ 2 ≤ labJ.n ∧ p ∣ 2 ^ labJ.n - 1

theorem ggLabelIso_c2_left {m : ℕ} {lab : LargeEvenLabel} (h : GGLabelIso ⟨.C, 2, m⟩ lab) :
    lab = ⟨.C, 2, m⟩ ∨ lab = ⟨.B, 2, m⟩ := by
  obtain ⟨t, r, n⟩ := lab
  rcases h with h | ⟨-, ht, hr, hn⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
  · exact Or.inl h.symm
  · simp only at ht hr hn
    subst hr hn
    rcases ht with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl rfl
  all_goals simp at h

theorem ggLabelIso_c2_right {m : ℕ} {lab : LargeEvenLabel} (h : GGLabelIso lab ⟨.C, 2, m⟩) :
    lab = ⟨.C, 2, m⟩ ∨ lab = ⟨.B, 2, m⟩ := by
  obtain ⟨t, r, n⟩ := lab
  rcases h with h | ⟨ht, -, hr, hn⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩
  · exact Or.inl h
  · simp only at ht hr hn
    subst hr hn
    rcases ht with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl rfl
  all_goals simp at h

theorem ggRegimeC2_not_pRankOne {p n : ℕ} {labJ labX : LargeEvenLabel}
    (h : GGRegimeC2 p n labJ labX) (lab : LargeEvenLabel) (hiso : GGLabelIso lab labJ) :
    ¬ GGTPNPRankOne p lab := by
  obtain ⟨ht, hr, -, -⟩ := h
  obtain ⟨tJ, rJ, m⟩ := labJ
  simp only at ht hr
  subst ht hr
  rcases ggLabelIso_c2_right hiso with rfl | rfl <;>
    rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -, -⟩) <;> simp at h

theorem ggTPNRankJ_of_c2 (hrig : GGLabelRigidInput) {Y : Type} [Group Y] {J : Subgroup Y}
    {labJ : LargeEvenLabel} (ht : labJ.tag = .C) (hr : labJ.rank = 2)
    (hΛ : LargeEvenInLambda2 labJ) (hhJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J)) :
    GGTPNRankJ J := by
  intro lab hlab hhas hrk
  obtain ⟨tJ, rJ, m⟩ := labJ
  simp only at ht hr
  subst ht hr
  rcases ggLabelIso_c2_left (hrig _ lab _ hΛ hlab hhJ hhas) with rfl | rfl <;>
    rcases hrk with ⟨h, -⟩ | ⟨h, -⟩ <;> simp at h

@[expose] def GGC2ExcRERK : Prop :=
  GGTablePKnownRK fun p n labJ labX => GGRegimeC2 p n labJ labX ∧ GGKacRE labX p

end CFSG.StandardType

end
