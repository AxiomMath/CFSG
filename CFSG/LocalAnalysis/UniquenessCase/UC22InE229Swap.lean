module

public import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Tactic.Group

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22ine229_mem_normalizer_of_gen {T T₀ : Subgroup G} (hT₀T : T₀ ≤ T) {t : G}
    (htT : t ∈ T) (hgen : ∀ x ∈ T, x ∈ T₀ ∨ t⁻¹ * x ∈ T₀) : t ∈ normalizer (T₀ : Set G) := by
  refine mem_normalizer_fintype fun y hy => ?_
  rcases hgen _ (mul_mem (mul_mem htT (hT₀T hy)) (inv_mem htT)) with h | h
  · exact h
  · rw [show t⁻¹ * (t * y * t⁻¹) = y * t⁻¹ by group] at h
    have ht : t⁻¹ ∈ T₀ := by
      have h1 := mul_mem (inv_mem hy) h
      rwa [inv_mul_cancel_left] at h1
    exact mul_mem (mul_mem (inv_mem_iff.1 ht) hy) ht

theorem uc22ine229_mul_conj_mem_normalizer {T T₀ : Subgroup G} (hT₀T : T₀ ≤ T) {t : G}
    (htT : t ∈ T) (hgen : ∀ x ∈ T, x ∈ T₀ ∨ t⁻¹ * x ∈ T₀) {h : G}
    (hh : h ∈ normalizer (T₀ : Set G))
    (hcomm : h * (t * h * t⁻¹) * h⁻¹ * (t * h * t⁻¹)⁻¹ ∈ T) :
    h * (t * h * t⁻¹) ∈ normalizer (T : Set G) := by
  have htN := uc22ine229_mem_normalizer_of_gen hT₀T htT hgen
  have huN : t * h * t⁻¹ ∈ normalizer (T₀ : Set G) := mul_mem (mul_mem htN hh) (inv_mem htN)
  have hdN : h * (t * h * t⁻¹) ∈ normalizer (T₀ : Set G) := mul_mem hh huN
  have ht2 : t * t ∈ T₀ := by
    rcases hgen _ (mul_mem htT htT) with h2 | h2
    · exact h2
    · rw [inv_mul_cancel_left] at h2
      exact mul_mem h2 h2
  have hs : h * (t * t) * h⁻¹ * (t * t)⁻¹ ∈ T₀ :=
    mul_mem ((mem_normalizer_iff.1 hh _).1 ht2) (inv_mem ht2)
  have hdt : h * (t * h * t⁻¹) * t * (h * (t * h * t⁻¹))⁻¹ ∈ T := by
    rw [show h * (t * h * t⁻¹) * t * (h * (t * h * t⁻¹))⁻¹ =
        h * (t * h * t⁻¹) * h⁻¹ * (t * h * t⁻¹)⁻¹ *
          ((t * h * t⁻¹) * (h * (t * t) * h⁻¹ * (t * t)⁻¹) * (t * h * t⁻¹)⁻¹) * t by group]
    exact mul_mem (mul_mem hcomm (hT₀T ((mem_normalizer_iff.1 huN _).1 hs))) htT
  refine mem_normalizer_fintype fun x hx => ?_
  rcases hgen x hx with h0 | h0
  · exact hT₀T ((mem_normalizer_iff.1 hdN x).1 h0)
  · rw [show h * (t * h * t⁻¹) * x * (h * (t * h * t⁻¹))⁻¹ =
        h * (t * h * t⁻¹) * t * (h * (t * h * t⁻¹))⁻¹ *
          (h * (t * h * t⁻¹) * (t⁻¹ * x) * (h * (t * h * t⁻¹))⁻¹) by group]
    exact mul_mem hdt (hT₀T ((mem_normalizer_iff.1 hdN _).1 h0))

end CFSG.LocalAnalysis.UniquenessCase.UC22
