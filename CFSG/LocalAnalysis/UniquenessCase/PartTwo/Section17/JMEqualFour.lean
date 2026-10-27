module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.JMFour
public import CFSG.LocalAnalysis.ComponentClassification.EvenLieFieldExponent

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.ComponentClassification.CatLeafProof

variable {G : Type} [Group G] [Finite G]

section JMEqualFour


private theorem false_of_calL1Shape_of_isL2_or_isU3 {Y : Type} [Group Y]
    {t : StatedLieTag} {m f : ℕ} (h : LieModel Y t m 2 f)
    (hsh : (t = .G2 ∧ m = 0) ∨ (t = .PSp ∧ m = 2) ∨
      (t = .PSU ∧ m = 4) ∨ (t = .PSU ∧ m = 5))
    (hLU : ∃ n, IsL2 Y n ∨ IsU3 Y n) : False := by
  obtain ⟨n, hL2 | hU3⟩ := hLU
  · have h' := lieModel_eq_of_isChar2LieShape hL2 (Or.inl ⟨rfl, rfl⟩) h
    rcases hsh with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd h'.1 (by decide)
    · exact absurd h'.1 (by decide)
    · exact absurd h'.1 (by decide)
    · exact absurd h'.1 (by decide)
  · have h' := lieModel_eq_of_isChar2LieShape hU3 (Or.inr (Or.inl ⟨rfl, rfl⟩)) h
    rcases hsh with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd h'.1 (by decide)
    · exact absurd h'.1 (by decide)
    · exact absurd h'.2.1 (by omega)
    · exact absurd h'.2.1 (by omega)

theorem jM_eq_four_of_mem_calL0Star {D : Data G} {p : ℕ} {X : Subgroup G}
    (hX0 : X ∈ calL0Star D p) (hXp : X ∈ calLp D p)
    (hs : IsSimpleGroup (Bar2 X)) (hnotalt : ¬ IsAlt (Bar2 X) 5)
    (hLU : ∃ n, IsL2 (Bar2 X) n ∨ IsU3 (Bar2 X) n) : jM D p = 4 := by
  have hmain := jM_mem_of_nonempty (D := D) (p := p) ⟨X, hX0⟩
  have hcases : jM D p = 1 ∨ jM D p = 2 ∨ jM D p = 3 ∨ jM D p = 4 ∨ jM D p = 5 := by
    omega
  rcases hcases with h | h | h | h | h
  · exfalso
    have hX1 : X ∈ calL1Star D p := by simpa [calL0Star, calLjStar, h] using hX0
    rw [mem_calL1Star] at hX1
    rcases hX1.2 with ⟨f, hG2 | hSp4 | hU4⟩ | hU5
    · exact false_of_calL1Shape_of_isL2_or_isU3 hG2 (Or.inl ⟨rfl, rfl⟩) hLU
    · exact false_of_calL1Shape_of_isL2_or_isU3 hSp4 (Or.inr (Or.inl ⟨rfl, rfl⟩)) hLU
    · exact false_of_calL1Shape_of_isL2_or_isU3 hU4
        (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) hLU
    · exact false_of_calL1Shape_of_isL2_or_isU3 hU5
        (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))) hLU
  · exfalso
    have hX2 : X ∈ calL2Star D p := by simpa [calL0Star, calLjStar, h] using hX0
    rw [mem_calL2Star] at hX2
    exact hX2.2.1 hXp
  · exfalso
    have hX3 : X ∈ calL3Star D p := by simpa [calL0Star, calLjStar, h] using hX0
    rw [mem_calL3Star] at hX3
    exact not_isSimpleGroup_of_isA5xA5 hs hX3.2
  · exact h
  · exfalso
    have hX5 : X ∈ calL5Star D p := by simpa [calL0Star, calLjStar, h] using hX0
    rw [mem_calL5Star] at hX5
    exact hnotalt hX5.2

end JMEqualFour

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
