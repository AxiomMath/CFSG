module

public import CFSG.LocalAnalysis.StandardType.GGTPNRegimeDefs
public import CFSG.LocalAnalysis.StandardType.GGKacK0V2
public import CFSG.LocalAnalysis.StandardType.GGTPNThmUTableClDefs
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGA24ExcPairRK : Prop :=
  GGTablePKnownRK fun p n labJ labX => GGRegimeA24 p n labJ labX ∧ GGKacExcPair labX p

theorem ggA24_regime_not_rankOne (p n : ℕ) (labJ labX : LargeEvenLabel)
    (h : GGRegimeA24 p n labJ labX) (lab : LargeEvenLabel) (hiso : GGLabelIso lab labJ) :
    ¬ GGTPNPRankOne p lab := by
  obtain ⟨rfl, rfl⟩ := h
  intro hrk
  simp only [GGLabelIso] at hiso
  simp only [GGTPNPRankOne] at hrk
  rcases hiso with rfl | ⟨-, h, -⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩
  · rcases hrk with ⟨-, h2⟩ | ⟨h1, -⟩ | ⟨-, -, h3⟩ | ⟨h1, -⟩
    · exact absurd h2 (by decide)
    · exact absurd h1 (by decide)
    · exact absurd h3 (by decide)
    · exact absurd h1 (by decide)
  all_goals simp at h

theorem ggTPNRankJ_of_a24 (hrig : GGLabelRigidInput) {Y : Type} [Group Y] {J : Subgroup Y}
    {p n : ℕ} {labJ labX : LargeEvenLabel} (hΛ : LargeEvenInLambda2 labJ)
    (hreg : GGRegimeA24 p n labJ labX) (hhJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J)) :
    GGTPNRankJ J := by
  intro lab hlab hhas hrk
  have hiso : GGLabelIso lab labJ := hrig lab labJ (↥J ⧸ Subgroup.center ↥J) hlab hΛ hhas hhJ
  refine ggA24_regime_not_rankOne p n labJ labX hreg lab hiso ?_
  rcases hrk with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

end CFSG.StandardType

end
