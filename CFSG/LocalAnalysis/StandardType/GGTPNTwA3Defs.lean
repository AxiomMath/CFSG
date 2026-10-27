module

public import CFSG.LocalAnalysis.StandardType.GGExcRERegimeDefs
public import CFSG.LocalAnalysis.StandardType.GGTPNThmRABase
public import CFSG.LocalAnalysis.StandardType.GGTPNThmUTableClDefs
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGRegimeTwA3 : ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → Prop :=
  fun p _ labJ _ => labJ.tag = .twA ∧ labJ.rank = 3 ∧ 2 ≤ labJ.n ∧ p ∣ 2 ^ labJ.n - 1

theorem ggLabelIso_twA3_left {m : ℕ} {lab : LargeEvenLabel} (h : GGLabelIso ⟨.twA, 3, m⟩ lab) :
    lab = ⟨.twA, 3, m⟩ ∨ lab = ⟨.twD, 3, m⟩ := by
  obtain ⟨t, r, n⟩ := lab
  unfold GGLabelIso at h
  simp only [LargeEvenLabel.mk.injEq, reduceCtorEq, false_and, and_false, or_false,
    false_or] at h
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨-, rfl, rfl, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem ggLabelIso_twA3_right {m : ℕ} {lab : LargeEvenLabel} (h : GGLabelIso lab ⟨.twA, 3, m⟩) :
    lab = ⟨.twA, 3, m⟩ ∨ lab = ⟨.twD, 3, m⟩ := by
  obtain ⟨t, r, n⟩ := lab
  unfold GGLabelIso at h
  simp only [LargeEvenLabel.mk.injEq, reduceCtorEq, false_and, and_false, or_false,
    false_or] at h
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨⟨rfl, rfl, -⟩, -, -, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem ggRegimeTwA3_not_pRankOne {p n : ℕ} {labJ labX : LargeEvenLabel}
    (h : GGRegimeTwA3 p n labJ labX) (lab : LargeEvenLabel) (hiso : GGLabelIso lab labJ) :
    ¬ GGTPNPRankOne p lab := by
  obtain ⟨ht, hr, -, -⟩ := h
  obtain ⟨tJ, rJ, m⟩ := labJ
  simp only at ht hr
  subst ht hr
  rcases ggLabelIso_twA3_right hiso with rfl | rfl <;>
    rintro (⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩ | ⟨-, h, -⟩) <;> simp at h

theorem ggTPNRankJ_of_twA3 (hrig : GGLabelRigidInput) {Y : Type} [Group Y] {J : Subgroup Y}
    {labJ : LargeEvenLabel} (ht : labJ.tag = .twA) (hr : labJ.rank = 3)
    (hΛ : LargeEvenInLambda2 labJ) (hhJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J)) :
    GGTPNRankJ J := by
  intro lab hlab hhas hrk
  obtain ⟨tJ, rJ, m⟩ := labJ
  simp only at ht hr
  subst ht hr
  rcases ggLabelIso_twA3_left (hrig _ lab _ hΛ hlab hhJ hhas) with rfl | rfl <;>
    rcases hrk with ⟨h, -⟩ | ⟨-, h⟩ <;> simp at h

@[expose] def GGTwA3ExcRERK : Prop :=
  GGTablePKnownRK fun p n labJ labX => GGRegimeTwA3 p n labJ labX ∧ GGKacRE labX p

end CFSG.StandardType

end
