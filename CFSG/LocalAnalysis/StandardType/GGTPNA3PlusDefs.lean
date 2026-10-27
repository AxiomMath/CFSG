module

public import CFSG.LocalAnalysis.StandardType.GGExcRERegimeDefs
public import CFSG.LocalAnalysis.StandardType.GGTPNThmRABase
public import CFSG.LocalAnalysis.StandardType.GGTPNThmUTableClDefs
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGRegimeA3Plus : ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → Prop :=
  fun p _ labJ _ => labJ.tag = .A ∧ labJ.rank = 3 ∧ 2 ≤ labJ.n ∧ p ∣ 2 ^ labJ.n + 1

theorem ggLabelIso_a3_left {m : ℕ} {lab : LargeEvenLabel} (h : GGLabelIso ⟨.A, 3, m⟩ lab) :
    lab = ⟨.A, 3, m⟩ ∨ lab = ⟨.D, 3, m⟩ := by
  obtain ⟨t, r, n⟩ := lab
  unfold GGLabelIso at h
  rcases h with h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
  · exact Or.inl h.symm
  · rcases h with h | h <;> cases h
  · simp at h
  · exact Or.inr h
  · simp at h
  · simp at h
  · simp at h
  · simp at h

theorem ggLabelIso_a3_right {m : ℕ} {lab : LargeEvenLabel} (h : GGLabelIso lab ⟨.A, 3, m⟩) :
    lab = ⟨.A, 3, m⟩ ∨ lab = ⟨.D, 3, m⟩ := by
  obtain ⟨t, r, n⟩ := lab
  unfold GGLabelIso at h
  rcases h with h | ⟨-, h, -⟩ | ⟨h, h'⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩
  · exact Or.inl h
  · rcases h with h | h <;> cases h
  · simp only [LargeEvenLabel.mk.injEq] at h h'
    obtain ⟨rfl, rfl, -⟩ := h
    obtain ⟨-, -, rfl⟩ := h'
    exact Or.inr rfl
  · simp at h
  · simp at h
  · simp at h
  · simp at h
  · simp at h

theorem ggRegimeA3Plus_not_pRankOne {p n : ℕ} {labJ labX : LargeEvenLabel}
    (h : GGRegimeA3Plus p n labJ labX) (lab : LargeEvenLabel) (hiso : GGLabelIso lab labJ) :
    ¬ GGTPNPRankOne p lab := by
  obtain ⟨ht, hr, -, -⟩ := h
  obtain ⟨tJ, rJ, m⟩ := labJ
  simp only at ht hr
  subst ht hr
  rcases ggLabelIso_a3_right hiso with rfl | rfl <;>
    rintro (⟨-, h⟩ | ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨h, -⟩) <;> simp at h

theorem ggTPNRankJ_of_a3 (hrig : GGLabelRigidInput) {Y : Type} [Group Y] {J : Subgroup Y}
    {labJ : LargeEvenLabel} (ht : labJ.tag = .A) (hr : labJ.rank = 3)
    (hΛ : LargeEvenInLambda2 labJ) (hhJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J)) :
    GGTPNRankJ J := by
  intro lab hlab hhas hrk
  obtain ⟨tJ, rJ, m⟩ := labJ
  simp only at ht hr
  subst ht hr
  rcases ggLabelIso_a3_left (hrig _ lab _ hΛ hlab hhJ hhas) with rfl | rfl <;>
    rcases hrk with ⟨-, h⟩ | ⟨-, h⟩ <;> simp at h

@[expose] def GGA3PlusExcRERK : Prop :=
  GGTablePKnownRK fun p n labJ labX => GGRegimeA3Plus p n labJ labX ∧ GGKacRE labX p

end CFSG.StandardType

end
