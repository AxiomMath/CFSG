module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_inverts {A B : Subgroup G} (hAB : A ≤ B) {t : G}
    (ht : ∀ x ∈ B, t * x * t⁻¹ = x⁻¹) : t ∈ normalizer (A : Set G) := by
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [ht h (hAB hh)]
    exact A.inv_mem hh
  · intro hh
    have hb : t * h * t⁻¹ ∈ B := hAB hh
    have h1 : t * (t * h * t⁻¹) * t⁻¹ = (t * h * t⁻¹)⁻¹ := ht _ hb
    have h3 : (t * h * t⁻¹)⁻¹ = t * h⁻¹ * t⁻¹ := by group
    rw [h3] at h1
    have h5 : t * h * t⁻¹ = h⁻¹ := mul_left_cancel (mul_right_cancel h1)
    have h6 : h⁻¹ ∈ A := by rw [← h5]; exact hh
    simpa using A.inv_mem h6

theorem s21_2 (D : Data G) (Ch : Choice2011 G) : S21_2 D Ch := by
  intro _ c A hA hle
  obtain ⟨_, _, B', C', _, _, _, _, _, _, ⟨t, _, htM, _, htinv⟩, _⟩ := c.hB
  exact htM (hle (mem_normalizer_of_inverts hA htinv))

end CFSG.LocalAnalysis.UniquenessCase.UC22
