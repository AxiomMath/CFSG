module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08Ce6Adapt
public import CFSG.LocalAnalysis.StandardType.GGDepED4LRead

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggQ2s08_ce6_twoNode_of_nonLevi (hRig : GGLabelRigidInput) {G : Type} [Group G]
    {J L X : Subgroup G} (hrowL : GGResRowAt ggRowTwoNodeSmallJD 3 J L)
    (hN : GGResRowAt ggRowNonLevi 3 J X) : GGResRowAt ggRowTwoNode 3 J X := by
  obtain ⟨labJ, labL, hJΛ, hLΛ, hJl, hLl, hrowS⟩ := hrowL
  unfold ggRowTwoNodeSmallJD ggRowTwoNodeSmall at hrowS
  obtain ⟨⟨hrowL2, _⟩, hJtag⟩ := hrowS
  have hlabJ : labJ = ⟨.D, 4, labJ.n⟩ := by
    rcases hrowL2 with hA | htwA | hD4 | htwD4
    · rw [hA.1] at hJtag; exact absurd hJtag (by decide)
    · rw [htwA.1] at hJtag; exact absurd hJtag (by decide)
    · exact hD4.1
    · exact htwD4.1
  have key : ∀ {R : ℕ → LargeEvenLabel → LargeEvenLabel → Prop}, GGResRowAt R 3 J X →
      ∃ a b : LargeEvenLabel, R 3 a b ∧ a.tag = .D := by
    intro R h
    obtain ⟨labJ', labX', hJ'Λ, hXΛ, hJ'l, hXl, hr⟩ := h
    refine ⟨labJ', labX', hr, ?_⟩
    have hiso : GGLabelIso labJ labJ' := hRig labJ labJ' _ hJΛ hJ'Λ hJl hJ'l
    rw [← ggTWR_iso_eq_D4 hiso hlabJ]
    exact hJtag
  rcases GGResRowAt.cases hN with h2 | h3 | h4 | h5 | h6 | h7
  · exact h2
  · exfalso
    obtain ⟨a, b, hr, hD⟩ := key h3
    rcases hr with ⟨hA, -⟩ | ⟨hA, -⟩ <;> (rw [hA] at hD; simp at hD)
  · exfalso
    obtain ⟨a, b, hr, hD⟩ := key h4
    rcases hr with ⟨hT, -⟩ | ⟨hT, -⟩ <;> (rw [hT] at hD; exact absurd hD (by decide))
  · exfalso
    obtain ⟨a, b, hr, hD⟩ := key h5
    rw [hr.1] at hD
    exact absurd hD (by decide)
  · exfalso
    obtain ⟨a, b, hr, hD⟩ := key h6
    exact absurd hr.1 (by norm_num)
  · exfalso
    obtain ⟨a, b, hr, hD⟩ := key h7
    rw [hr.1] at hD
    exact absurd hD (by decide)

theorem ggQ2s08_ce6_shape (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G]
    {Bs J L X : Subgroup G} (hrowL : GGResRowAt ggRowTwoNodeSmallJD 3 J L)
    (hXd : GGResXDatum 3 Bs X ∨ GGResRowAt ggRowSeven 3 J X)
    (hJ : GGResXDatum 3 Bs X → GGResSideDatum 3 Bs X J ∨ GGResLeviSideDatumLE3 3 Bs X J ∨
      GGResRowAt ggRowNonLevi 3 J X) :
    GGResSideDatum 3 Bs X J ∨ GGResLeviSideDatumLE3 3 Bs X J ∨ GGResRowAt ggRowTwoNode 3 J X := by
  rcases hXd with hX | hseven
  · rcases hJ hX with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (ggQ2s08_ce6_twoNode_of_nonLevi hRig hrowL h))
  · exfalso
    obtain ⟨_, _, _, _, _, _, hr⟩ := hseven
    exact absurd hr.1 (by norm_num)

end CFSG.StandardType

end
