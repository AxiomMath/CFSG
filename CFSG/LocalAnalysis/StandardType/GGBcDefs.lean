module

public import CFSG.LocalAnalysis.StandardType.GGTPNRegimeDefs
public import CFSG.LocalAnalysis.StandardType.GGKacK0V2
public import CFSG.LocalAnalysis.StandardType.GGTPNThmRABase
public import CFSG.LocalAnalysis.StandardType.GGTPNThmUTableClDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGBcClTypeARK : Prop :=
  GGTablePKnownRK fun p n labJ labX =>
    GGRegimeBC p n labJ labX ∧ (GGKacRA labX p ∨ (p = 5 ∧ labX = ⟨.A, 5, 2⟩))

@[expose] def GGBcExcPairRK : Prop :=
  GGTablePKnownRK fun p n labJ labX => GGRegimeBC p n labJ labX ∧ GGKacExcPair labX p

@[expose] def GGBcClRARK : Prop :=
  GGTablePKnownRK fun p n labJ labX => GGRegimeBC p n labJ labX ∧ GGKacRA labX p

@[expose] def GGBcClA5RK : Prop :=
  GGTablePKnownRK fun p n labJ labX => GGRegimeBC p n labJ labX ∧ (p = 5 ∧ labX = ⟨.A, 5, 2⟩)

theorem ggBc_regime_not_rankOne (p n : ℕ) (labJ labX : LargeEvenLabel)
    (h : GGRegimeBC p n labJ labX) (lab : LargeEvenLabel) (hiso : GGLabelIso lab labJ) :
    ¬ GGTPNPRankOne p lab := by
  obtain ⟨hBC, h3⟩ := h
  obtain ⟨t, r, m⟩ := labJ
  obtain ⟨t', r', m'⟩ := lab
  intro hrk
  simp only [GGLabelIso] at hiso
  simp only [GGTPNPRankOne] at hrk
  simp only at hBC h3
  rcases hiso with h | h | h | h | h | h | h | h
  · obtain ⟨rfl, rfl, rfl⟩ := h
    rcases hrk with ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2, -⟩ | ⟨-, h2, -⟩ <;> omega
  · obtain ⟨-, -, rfl, rfl⟩ := h
    rcases hrk with ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2, -⟩ | ⟨-, h2, -⟩ <;> omega
  all_goals simp_all

theorem ggTPNRankJ_of_bc (hrig : GGLabelRigidInput) {Y : Type} [Group Y] {J : Subgroup Y}
    {p n : ℕ} {labJ labX : LargeEvenLabel} (hΛ : LargeEvenInLambda2 labJ)
    (hreg : GGRegimeBC p n labJ labX) (hhJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J)) :
    GGTPNRankJ J := by
  intro lab hlab hhas hrk
  have hiso : GGLabelIso lab labJ := hrig lab labJ (↥J ⧸ Subgroup.center ↥J) hlab hΛ hhas hhJ
  refine ggBc_regime_not_rankOne p n labJ labX hreg lab hiso ?_
  rcases hrk with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

end CFSG.StandardType

end
