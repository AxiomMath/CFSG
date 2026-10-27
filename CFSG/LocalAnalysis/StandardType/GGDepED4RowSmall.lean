module

public import CFSG.LocalAnalysis.StandardType.GGDepED4ReadDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggDepED4_row_small_of_row (hRig : GGLabelRigidInput) {G : Type} [Group G] {p : ℕ}
    {J K L : Subgroup G} (hK : GGResRowAt ggRowTwoNodeSmallJD p J K)
    (hL : GGResRowAt ggRowTwoNode p J L) : GGResRowAt ggRowTwoNodeSmallJD p J L := by
  obtain ⟨labJ, labK, hJΛ, hKΛ, hJl, hKl, hRowK⟩ := hK
  obtain ⟨labJ', labL, hJ'Λ, hLΛ, hJ'l, hLl, hRowL⟩ := hL
  unfold ggRowTwoNodeSmallJD ggRowTwoNodeSmall at hRowK
  obtain ⟨⟨hrowK, _hKle⟩, hJtag⟩ := hRowK
  have hlabJ : labJ = ⟨.D, 4, labJ.n⟩ := by
    rcases hrowK with hA | htwA | hD4 | htwD4
    · rw [hA.1] at hJtag; exact absurd hJtag (by decide)
    · rw [htwA.1] at hJtag; exact absurd hJtag (by decide)
    · exact hD4.1
    · exact htwD4.1
  have hiso : GGLabelIso labJ labJ' :=
    hRig labJ labJ' (↥J ⧸ Subgroup.center ↥J) hJΛ hJ'Λ hJl hJ'l
  have hEqJ : labJ = labJ' := ggTWR_iso_eq_D4 hiso hlabJ
  have hJ'tag : labJ'.tag = .D := by rw [← hEqJ]; exact hJtag
  have hLrank : labL.rank ≤ 9 := by
    rcases hRowL with hA | htwA | hD4 | htwD4
    · rw [hJ'tag] at hA; exact absurd hA.1 (by decide)
    · rw [hJ'tag] at htwA; exact absurd htwA.1 (by decide)
    · obtain ⟨-, -, -, hX⟩ := hD4
      subst hX
      change (0 : ℕ) ≤ 9
      omega
    · obtain ⟨-, -, -, hX⟩ := htwD4
      subst hX
      change (0 : ℕ) ≤ 9
      omega
  exact ⟨labJ', labL, hJ'Λ, hLΛ, hJ'l, hLl, ⟨⟨hRowL, hLrank⟩, hJ'tag⟩⟩

end CFSG.StandardType

end
