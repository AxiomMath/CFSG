module

public import Mathlib.Data.Set.Card

public section

namespace CFSG.ASVolI.ChH

namespace ElemAb2Orbits

open Equiv

theorem perm_apply_eq_of_local {σ e : Perm (Fin 8)} {O : Set (Fin 8)} (hO : O.ncard ≤ 4)
    (hσ : ∀ y ∈ O, σ y ∈ O) (he : ∀ y ∈ O, e y ∈ O)
    (hσl : (∀ y ∈ O, σ y = y) ∨ ∀ y ∈ O, σ y ≠ y ∧ σ (σ y) = y)
    (hel : (∀ y ∈ O, e y = y) ∨ ∀ y ∈ O, e y ≠ y ∧ e (e y) = y)
    {ρ : Fin 8} (hρ : ρ ∈ O) (hag : σ ρ = e ρ) : ∀ z ∈ O, σ z = e z := by
  rcases hσl with hσl | hσl
  · rcases hel with hel | hel
    · intro z hz
      rw [hσl z hz, hel z hz]
    · exact absurd (hag.symm.trans (hσl ρ hρ)) (hel ρ hρ).1
  · rcases hel with hel | hel
    · exact absurd (hag.trans (hel ρ hρ)) (hσl ρ hρ).1
    · intro z hz
      by_cases h1 : z = ρ
      · rw [h1]
        exact hag
      by_cases h2 : z = σ ρ
      · calc σ z = ρ := by rw [h2]; exact (hσl ρ hρ).2
          _ = e (e ρ) := ((hel ρ hρ).2).symm
          _ = e z := by rw [h2, hag]
      have h3 : ρ ≠ σ ρ := (hσl ρ hρ).1.symm
      have hT : ({z, ρ, σ ρ} : Set (Fin 8)).ncard = 3 := by
        rw [Set.ncard_eq_three]
        exact ⟨z, ρ, σ ρ, h1, h2, h3, rfl⟩
      have hsub : ({z, ρ, σ ρ} : Set (Fin 8)) ⊆ O := by
        intro a ha
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
        rcases ha with rfl | rfl | rfl
        · exact hz
        · exact hρ
        · exact hσ ρ hρ
      have hle : (O \ {z, ρ, σ ρ}).ncard ≤ 1 := by
        rw [Set.ncard_diff hsub, hT]
        omega
      have hσz : σ z ∈ O \ {z, ρ, σ ρ} := by
        refine ⟨hσ z hz, ?_⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        refine ⟨(hσl z hz).1, fun h => h2 ?_, fun h => h1 (σ.injective h)⟩
        have := (hσl z hz).2
        rw [h] at this
        exact this.symm
      have hez : e z ∈ O \ {z, ρ, σ ρ} := by
        refine ⟨he z hz, ?_⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        refine ⟨(hel z hz).1, fun h => h2 ?_, fun h => h1 (e.injective (h.trans hag))⟩
        have := (hel z hz).2
        rw [h] at this
        rw [hag]
        exact this.symm
      exact (Set.ncard_le_one (Set.toFinite _)).mp hle _ hσz _ hez

end ElemAb2Orbits

end CFSG.ASVolI.ChH
