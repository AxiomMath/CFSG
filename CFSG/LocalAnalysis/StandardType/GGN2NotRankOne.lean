module

public import CFSG.LocalAnalysis.StandardType.GGN2Defs
public import CFSG.LocalAnalysis.StandardType.GGTPNThmUTableClDefs
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggN2_regime_not_rankOne (p n : ℕ) (labJ labX : LargeEvenLabel)
    (h : GGRegimeN2 p n labJ labX) (lab : LargeEvenLabel) (hiso : GGLabelIso lab labJ) :
    ¬ GGTPNPRankOne p lab := by
  obtain ⟨rfl, rfl, rfl⟩ := h
  intro hrk
  simp only [GGLabelIso] at hiso
  simp only [GGTPNPRankOne] at hrk
  rcases hiso with rfl | ⟨-, h, -⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨ha, hb⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩
  · rcases hrk with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, h2⟩
    · exact absurd h1 (by decide)
    · exact absurd h1 (by decide)
    · exact absurd h1 (by decide)
    · exact absurd h2 (by decide)
  · simp at h
  · simp at h
  · simp at h
  · rw [ha] at hrk
    rcases hrk with ⟨h1, -⟩ | ⟨-, h2⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
    · exact absurd h1 (by simp)
    · exact absurd h2 (by simp)
    · exact absurd h1 (by simp)
    · exact absurd h1 (by simp)
  · simp at h
  · simp at h
  · simp at h

theorem ggTPNRankJ_of_n2 (hrig : GGLabelRigidInput) {Y : Type} [Group Y] {J : Subgroup Y}
    {p n : ℕ} {labJ labX : LargeEvenLabel} (hΛ : LargeEvenInLambda2 labJ)
    (hreg : GGRegimeN2 p n labJ labX) (hhJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J)) :
    GGTPNRankJ J := by
  intro lab hlab hhas hrk
  have hiso : GGLabelIso lab labJ := hrig lab labJ (↥J ⧸ Subgroup.center ↥J) hlab hΛ hhas hhJ
  refine ggN2_regime_not_rankOne p n labJ labX hreg lab hiso ?_
  rcases hrk with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

end CFSG.StandardType

end
