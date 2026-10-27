module

public import CFSG.LocalAnalysis.StandardType.GGTPNTwA6Defs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGRegimeDeletedUnitary1836 :
    ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → Prop :=
  fun p n labJ _ => p = 3 ∧ ∃ d : ℕ, 5 ≤ d ∧ n = 3 ^ (d + 1) ∧ labJ = ⟨.twA, d - 1, 1⟩

theorem ggRegimeDeletedUnitary1836_of {d : ℕ} (hd : 5 ≤ d) (labN : LargeEvenLabel) :
    GGRegimeDeletedUnitary1836 3 (3 ^ (d + 1)) ⟨.twA, d - 1, 1⟩ labN :=
  ⟨rfl, d, hd, rfl, rfl⟩

theorem ggLabelIso_twA_left {r m : ℕ} (hr : 4 ≤ r) {lab : LargeEvenLabel}
    (h : GGLabelIso ⟨.twA, r, m⟩ lab) : lab = ⟨.twA, r, m⟩ := by
  obtain ⟨t, l, n⟩ := lab
  simp only [GGLabelIso] at h
  rcases h with h | h | h | h | h | h | h | h <;> simp_all

theorem ggLabelIso_twA_right {r m : ℕ} (hr : 4 ≤ r) {lab : LargeEvenLabel}
    (h : GGLabelIso lab ⟨.twA, r, m⟩) : lab = ⟨.twA, r, m⟩ := by
  obtain ⟨t, l, n⟩ := lab
  simp only [GGLabelIso] at h
  rcases h with h | h | h | h | h | h | h | h <;> simp_all

theorem ggRegimeDeletedUnitary1836_not_pRankOne {p n : ℕ} {labJ labX : LargeEvenLabel}
    (h : GGRegimeDeletedUnitary1836 p n labJ labX) (lab : LargeEvenLabel)
    (hiso : GGLabelIso lab labJ) : ¬ GGTPNPRankOne p lab := by
  obtain ⟨-, d, hd, -, hl⟩ := h
  subst hl
  rw [ggLabelIso_twA_right (r := d - 1) (by omega) hiso]
  rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h, -⟩)
  all_goals simp at h
  omega

theorem ggTPNRankJ_of_deletedUnitary1836 (hrig : GGLabelRigidInput) {Y : Type} [Group Y]
    {J : Subgroup Y} {labJ : LargeEvenLabel} {d : ℕ} (hd : 5 ≤ d)
    (hl : labJ = ⟨.twA, d - 1, 1⟩) (hΛ : LargeEvenInLambda2 labJ)
    (hhJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J)) : GGTPNRankJ J := by
  intro lab hlab hhas hrk
  subst hl
  rw [ggLabelIso_twA_left (r := d - 1) (by omega) (hrig _ lab _ hΛ hlab hhJ hhas)] at hrk
  rcases hrk with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h, -⟩
  all_goals simp at h

@[expose] def GGDelUExcOneThreeRK : Prop :=
  GGTablePKnownRK fun p n labJ labX =>
    GGRegimeDeletedUnitary1836 p n labJ labX ∧ GGKacExcPair labX p ∧ GGKacCentred labX p ∧
      labX.n = 1 ∧ p = 3

@[expose] def GGDelUE6ThreeRK : Prop :=
  GGTablePKnownRK fun p n labJ labX =>
    GGRegimeDeletedUnitary1836 p n labJ labX ∧ (labX.tag = .E6 ∨ labX.tag = .twE6) ∧ p = 3 ∧
      GGKacExcPair labX p

@[expose] def GGQTwoDE7SU6Cof : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (A Ab : Subgroup (MulAut X)) (σ : MulAut X)
    (J : Subgroup X) (n : ℕ),
    GGTPNDatumB 3 n (fun _ _ => True) A Ab σ J → GGTPNKernel A σ J →
    GGHasLabel ⟨.twA, 5, 1⟩ (↥J ⧸ Subgroup.center ↥J) →
    GGHasLabel ⟨.E7, 0, 1⟩ (X ⧸ Subgroup.center X) → n = 3 ^ 7 → False

end CFSG.StandardType

end
