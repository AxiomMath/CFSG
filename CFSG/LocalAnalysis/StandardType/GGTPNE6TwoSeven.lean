module

public import CFSG.LocalAnalysis.StandardType.GGExcTwoCompList
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ltqT7_contra
    (h : GGE6TwoSevenComp) {p n : ℕ} {S : ℕ → LargeEvenLabel → Prop}
    {X : Type} [Group X] [Finite X] {A Ab : Subgroup (MulAut X)} {σ : MulAut X}
    {J : Subgroup X} (hB : GGTPNBasicB p n S A Ab σ J) (labJ : LargeEvenLabel)
    (hΛ : LargeEvenInLambda2 labJ) (hJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (hA : ¬ GGLabelIso labJ ⟨.A, 2, 1⟩) (hT : ¬ GGLabelIso labJ ⟨.triD4, 0, 1⟩)
    (hp : p = 7) (hX : GGHasLabel ⟨.E6, 0, 1⟩ (X ⧸ Subgroup.center X)) : False := by
  subst hp
  have hrig : ∀ lab' : LargeEvenLabel, LargeEvenInLambda2 lab' →
      GGLabelIso ⟨.E6, 0, 1⟩ lab' → lab' = ⟨.E6, 0, 1⟩ := by
    intro lab' _ hiso
    simpa [GGLabelIso, eq_comm] using hiso
  obtain ⟨labJ', hS, hlab'⟩ := GGCompList.of_basicB h (by simp [LargeEvenInLambda2]) hrig hB hX
  have hmem : labJ' = ⟨.A, 2, 1⟩ ∨ labJ' = ⟨.triD4, 0, 1⟩ := by simpa using hS
  have hΛ' : LargeEvenInLambda2 labJ' := by
    rcases hmem with rfl | rfl <;> simp [LargeEvenInLambda2]
  have hiso := ggLabelRigidInput_holds labJ labJ' (↥J ⧸ Subgroup.center ↥J) hΛ hΛ' hJ hlab'
  rcases hmem with rfl | rfl
  · exact hA hiso
  · exact hT hiso

theorem ggTablePKnownR_e6TwoSevenOut
    (h : GGE6TwoSevenComp) :
    GGTablePKnownR GGRegimeE6TwoSevenOut := by
  intro p hp hp2 X _ _ A Ab σ J n hd labJ labX hΛJ hΛX hr hhJ hhX
  obtain ⟨hp7, hlabX, hA, hT⟩ := hr
  have hX : GGHasLabel ⟨.E6, 0, 1⟩ (X ⧸ Subgroup.center X) := by
    rw [← hlabX]; exact hhX
  exact (ltqT7_contra h hd.1 labJ hΛJ hhJ hA hT hp7 hX).elim

theorem ggRegimeE6TwoSevenOut_of_two_le {p n : ℕ} {labJ labX : LargeEvenLabel} (hp : p = 7)
    (hX : labX = ⟨.E6, 0, 1⟩) (hn : 2 ≤ labJ.n) : GGRegimeE6TwoSevenOut p n labJ labX := by
  obtain ⟨t, r, m⟩ := labJ
  change 2 ≤ m at hn
  refine ⟨hp, hX, ?_, ?_⟩
  · intro h
    simp [GGLabelIso] at h
    omega
  · intro h
    simp [GGLabelIso] at h
    omega

theorem ggRegimeE6TwoSevenOut_of_BC {p n : ℕ} {labJ labX : LargeEvenLabel} (hp : p = 7)
    (hX : labX = ⟨.E6, 0, 1⟩) (hBC : labJ.tag = .B ∨ labJ.tag = .C) :
    GGRegimeE6TwoSevenOut p n labJ labX := by
  obtain ⟨t, r, m⟩ := labJ
  change t = .B ∨ t = .C at hBC
  rcases hBC with ht | ht <;> subst t <;>
    refine ⟨hp, hX, ?_, ?_⟩ <;> intro h <;> simp [GGLabelIso] at h

theorem ggTPNHalfJ_e6TwoSeven
    (h : GGE6TwoSevenComp) {p n : ℕ} {S : ℕ → LargeEvenLabel → Prop}
    {X : Type} [Group X] [Finite X] {A Ab : Subgroup (MulAut X)} {σ : MulAut X}
    {J : Subgroup X} (hB : GGTPNBasicB p n S A Ab σ J) (labJ : LargeEvenLabel)
    (hΛ : LargeEvenInLambda2 labJ) (hJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (hA : ¬ GGLabelIso labJ ⟨.A, 2, 1⟩) (hT : ¬ GGLabelIso labJ ⟨.triD4, 0, 1⟩) :
    p = 7 → GGHasLabel ⟨.E6, 0, 1⟩ (X ⧸ Subgroup.center X) → GGTPNHalfJ p J := by
  intro hp hX
  exact (ltqT7_contra h hB labJ hΛ hJ hA hT hp hX).elim

end CFSG.StandardType

end
