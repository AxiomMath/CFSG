module

public import CFSG.LocalAnalysis.StandardType.GGTWSmallADefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l05nS1_iso_eq_of_tag {lab lab' : LargeEvenLabel} (hiso : GGLabelIso lab lab')
    (hlab : lab.tag = .A ∨ lab.tag = .twA) (hlab' : lab'.tag = .A ∨ lab'.tag = .twA) :
    lab = lab' := by
  rcases hiso with h | ⟨h1, -, -, -⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact h
  · rcases hlab with ht | ht <;> rw [ht] at h1 <;> exact absurd h1 (by decide)
  · have htD : lab.tag = .D := by rw [h1]
    rcases hlab with ht | ht <;> rw [htD] at ht <;> exact absurd ht (by decide)
  · have htD : lab'.tag = .D := by rw [h2]
    rcases hlab' with ht | ht <;> rw [htD] at ht <;> exact absurd ht (by decide)
  · have htD : lab.tag = .twD := by rw [h1]
    rcases hlab with ht | ht <;> rw [htD] at ht <;> exact absurd ht (by decide)
  · have htD : lab'.tag = .twD := by rw [h2]
    rcases hlab' with ht | ht <;> rw [htD] at ht <;> exact absurd ht (by decide)
  · have htD : lab.tag = .twD := by rw [h1]
    rcases hlab with ht | ht <;> rw [htD] at ht <;> exact absurd ht (by decide)
  · have htD : lab'.tag = .twD := by rw [h1]
    rcases hlab' with ht | ht <;> rw [htD] at ht <;> exact absurd ht (by decide)

theorem ggTWSmallA_row_small_of_row (hRig : GGLabelRigidInput) {G : Type} [Group G] {p : ℕ}
    {J K L : Subgroup G} (hK : GGResRowAt ggRowTwoNodeSmallJA p J K)
    (hL : GGResRowAt ggRowTwoNode p J L) : GGResRowAt ggRowTwoNodeSmallJA p J L := by
  obtain ⟨labJ, labK, hJΛ, hKΛ, hJl, hKl, hRowK⟩ := hK
  obtain ⟨labJ', labL, hJ'Λ, hLΛ, hJ'l, hLl, hRowL⟩ := hL
  unfold ggRowTwoNodeSmallJA ggRowTwoNodeSmall at hRowK
  obtain ⟨⟨hrowK, hKle⟩, hJtag⟩ := hRowK
  have hiso : GGLabelIso labJ labJ' :=
    hRig labJ labJ' (↥J ⧸ Subgroup.center ↥J) hJΛ hJ'Λ hJl hJ'l
  have hJ'tag : labJ'.tag = .A ∨ labJ'.tag = .twA := by
    rcases hRowL with hA | htwA | hD4 | htwD4
    · exact Or.inl hA.1
    · exact Or.inr htwA.1
    · have hrank : 4 ≤ labJ'.rank := by rw [hD4.1]
      have hEq := ggTWR_iso_eq_fst hiso hJtag hrank
      have htagD : labJ.tag = .D := by rw [hEq, hD4.1]
      rcases hJtag with h | h <;> rw [htagD] at h <;> exact absurd h (by decide)
    · have hrank : 4 ≤ labJ'.rank := by rw [htwD4.1]
      have hEq := ggTWR_iso_eq_fst hiso hJtag hrank
      have htagD : labJ.tag = .D := by rw [hEq, htwD4.1]
      rcases hJtag with h | h <;> rw [htagD] at h <;> exact absurd h (by decide)
  have hEqJ : labJ' = labJ := (l05nS1_iso_eq_of_tag hiso hJtag hJ'tag).symm
  have hJrank_le : labJ.rank ≤ 7 := by
    rcases hrowK with ⟨-, -, -, hX⟩ | ⟨-, -, -, hX⟩ | ⟨hD, -, -, hX⟩ | ⟨hD, -, -, hX⟩
    · subst hX
      change labJ.rank + 2 ≤ 9 at hKle
      omega
    · subst hX
      change labJ.rank + 2 ≤ 9 at hKle
      omega
    · have htagD : labJ.tag = .D := by rw [hD]
      rcases hJtag with h | h <;> rw [htagD] at h <;> exact absurd h (by decide)
    · have htagD : labJ.tag = .D := by rw [hD]
      rcases hJtag with h | h <;> rw [htagD] at h <;> exact absurd h (by decide)
  have hLrank : labL.rank ≤ 9 := by
    rcases hRowL with ⟨-, -, -, hX⟩ | ⟨-, -, -, hX⟩ | ⟨-, -, -, hX⟩ | ⟨-, -, -, hX⟩
    · subst hX
      change labJ'.rank + 2 ≤ 9
      rw [hEqJ]
      omega
    · subst hX
      change labJ'.rank + 2 ≤ 9
      rw [hEqJ]
      omega
    · subst hX
      change (0 : ℕ) ≤ 9
      omega
    · subst hX
      change (0 : ℕ) ≤ 9
      omega
  exact ⟨labJ', labL, hJ'Λ, hLΛ, hJ'l, hLl, ⟨⟨hRowL, hLrank⟩, hJ'tag⟩⟩

end CFSG.StandardType

end
