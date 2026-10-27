module

public import CFSG.LocalAnalysis.StandardType.GGTPNLineDefs
import CFSG.LocalAnalysis.StandardType.GGTypeANbrRowFilter

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGRegimeTwA6 : ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → Prop :=
  fun p n labJ _ => p = 3 ∧ n ≤ 3 ^ 8 ∧ labJ.tag = .twA ∧ labJ.rank = 6 ∧ 3 ∣ 2 ^ labJ.n + 1

theorem ggLabelIso_twA6_left {m : ℕ} {lab : LargeEvenLabel} (h : GGLabelIso ⟨.twA, 6, m⟩ lab) :
    lab = ⟨.twA, 6, m⟩ := by
  obtain ⟨t, r, n⟩ := lab
  unfold GGLabelIso at h
  rcases h with h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
  · exact h.symm
  · rcases h with h | h <;> cases h
  all_goals simp at h

theorem ggLabelIso_twA6_right {m : ℕ} {lab : LargeEvenLabel} (h : GGLabelIso lab ⟨.twA, 6, m⟩) :
    lab = ⟨.twA, 6, m⟩ := by
  obtain ⟨t, r, n⟩ := lab
  unfold GGLabelIso at h
  rcases h with h | ⟨-, h, -⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩
  · exact h
  · rcases h with h | h <;> cases h
  all_goals simp at h

theorem ggRegimeTwA6_not_pRankOne {p n : ℕ} {labJ labX : LargeEvenLabel}
    (h : GGRegimeTwA6 p n labJ labX) (lab : LargeEvenLabel) (hiso : GGLabelIso lab labJ) :
    ¬ GGTPNPRankOne p lab := by
  obtain ⟨-, -, ht, hr, -⟩ := h
  obtain ⟨tJ, rJ, m⟩ := labJ
  simp only at ht hr
  subst ht hr
  rw [ggLabelIso_twA6_right hiso]
  rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h, -⟩) <;> simp at h

theorem ggTPNRankJ_of_twA6 (hrig : GGLabelRigidInput) {Y : Type} [Group Y] {J : Subgroup Y}
    {labJ : LargeEvenLabel} (ht : labJ.tag = .twA) (hr : labJ.rank = 6)
    (hΛ : LargeEvenInLambda2 labJ) (hhJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J)) :
    GGTPNRankJ J := by
  intro lab hlab hhas hrk
  obtain ⟨tJ, rJ, m⟩ := labJ
  simp only at ht hr
  subst ht hr
  rw [ggLabelIso_twA6_left (hrig _ lab _ hΛ hlab hhJ hhas)] at hrk
  rcases hrk with ⟨h, -⟩ | ⟨h, -⟩ <;> simp at h

theorem ggTablePRow_three_twA6 {n : ℕ} (hn : 3 ∣ 2 ^ n + 1) {X : LargeEvenLabel}
    (h : GGTablePRow 3 ⟨.twA, 6, n⟩ X) :
    X = ⟨.twA, 7, n⟩ ∨ X = ⟨.twA, 8, n⟩ ∨ X = ⟨.C, 7, n⟩ ∨ X = ⟨.twD, 7, n⟩ ∨
      X = ⟨.twD, 8, n⟩ ∨ (X.tag = .twE6 ∧ 3 * X.n = n) ∨ X = ⟨.E7, 0, n⟩ := by
  unfold GGTablePRow at h
  norm_num at h
  rcases h with ⟨hsub, -⟩ | ⟨-, h⟩
  · exact (not_dvd_two_pow_sub_add (by norm_num) Nat.prime_three hsub hn).elim
  · exact h

@[expose] def GGTwA6ExcOneThreeRK : Prop :=
  GGTablePKnownRK fun p n labJ labX =>
    GGRegimeTwA6 p n labJ labX ∧ GGKacExcPair labX p ∧ GGKacCentred labX p ∧ labX.n = 1 ∧ p = 3

@[expose] def GGTwA6E6ThreeRK : Prop :=
  GGTablePKnownRK fun p n labJ labX =>
    GGRegimeTwA6 p n labJ labX ∧ (labX.tag = .E6 ∨ labX.tag = .twE6) ∧ p = 3 ∧
      GGKacExcPair labX p

end CFSG.StandardType

end
