module

public import CFSG.Quasithin.Vol2.Ch11SecO10X
public import CFSG.Quasithin.H13.A7Offender

public section

namespace CFSG.Quasithin.Vol2.Ch11.O10

open Equiv Equiv.Perm Subgroup CFSG.Quasithin.SteinbergCB CFSG.Quasithin.H13.A7

theorem word_conj_kappa01 : ∀ u, IsTP (sevenWord u * ((swap 0 2 * swap 1 3) * swap 0 1 *
    (swap 0 2 * swap 1 3)⁻¹) * (sevenWord u)⁻¹) ∧ sevenWord u * ((swap 0 2 * swap 1 3) *
    swap 0 1 * (swap 0 2 * swap 1 3)⁻¹) * (sevenWord u)⁻¹ ≠ swap 0 1 := by
  decide +kernel

theorem word_conj_kappa23 : ∀ u, IsTP (sevenWord u * ((swap 0 2 * swap 1 3) * swap 2 3 *
    (swap 0 2 * swap 1 3)⁻¹) * (sevenWord u)⁻¹) ∧ sevenWord u * ((swap 0 2 * swap 1 3) *
    swap 2 3 * (swap 0 2 * swap 1 3)⁻¹) * (sevenWord u)⁻¹ ≠ swap 2 3 := by
  decide +kernel

theorem word_conj_kappa45 : ∀ u, IsTP (sevenWord u * ((swap 0 4 * swap 1 5) * swap 4 5 *
    (swap 0 4 * swap 1 5)⁻¹) * (sevenWord u)⁻¹) ∧ sevenWord u * ((swap 0 4 * swap 1 5) *
    swap 4 5 * (swap 0 4 * swap 1 5)⁻¹) * (sevenWord u)⁻¹ ≠ swap 4 5 := by
  decide +kernel

theorem exists_kappa {τ : Perm (Fin 7)} (hτ : IsTP τ) :
    ∃ κ ∈ alternatingGroup (Fin 7),
      (∀ u, InT3 (sevenWord u) →
        InT3 (κ * sevenWord u * κ⁻¹) ∧ sevenCond (κ * sevenWord u * κ⁻¹)) ∧
      ∀ σ ∈ sevenP, IsTP (σ * (κ * τ * κ⁻¹) * σ⁻¹) ∧ σ * (κ * τ * κ⁻¹) * σ⁻¹ ≠ τ := by
  rcases hτ with rfl | rfl | rfl
  · refine ⟨swap 0 2 * swap 1 3, mem_alternatingGroup.2 (by decide), conj23_inT3,
      fun σ hσ => ?_⟩
    obtain ⟨u, rfl⟩ := exists_word_of_mem_sevenP hσ
    exact word_conj_kappa01 u
  · refine ⟨swap 0 2 * swap 1 3, mem_alternatingGroup.2 (by decide), conj23_inT3,
      fun σ hσ => ?_⟩
    obtain ⟨u, rfl⟩ := exists_word_of_mem_sevenP hσ
    exact word_conj_kappa23 u
  · refine ⟨swap 0 4 * swap 1 5, mem_alternatingGroup.2 (by decide), conj45_inT3,
      fun σ hσ => ?_⟩
    obtain ⟨u, rfl⟩ := exists_word_of_mem_sevenP hσ
    exact word_conj_kappa45 u

theorem exists_disjoint_swaps {τ τ' : Perm (Fin 7)} (hτ : IsTP τ) (hτ' : IsTP τ')
    (hne : τ' ≠ τ) : ∃ a b c d : Fin 7, τ = swap a b ∧ τ' = swap c d ∧ a ≠ b ∧ c ≠ a ∧
      d ≠ a ∧ c ≠ d := by
  rcases hτ with rfl | rfl | rfl <;> rcases hτ' with rfl | rfl | rfl
  · exact absurd rfl hne
  · exact ⟨0, 1, 2, 3, rfl, rfl, by decide, by decide, by decide, by decide⟩
  · exact ⟨0, 1, 4, 5, rfl, rfl, by decide, by decide, by decide, by decide⟩
  · exact ⟨2, 3, 0, 1, rfl, rfl, by decide, by decide, by decide, by decide⟩
  · exact absurd rfl hne
  · exact ⟨2, 3, 4, 5, rfl, rfl, by decide, by decide, by decide, by decide⟩
  · exact ⟨4, 5, 0, 1, rfl, rfl, by decide, by decide, by decide, by decide⟩
  · exact ⟨4, 5, 2, 3, rfl, rfl, by decide, by decide, by decide, by decide⟩
  · exact absurd rfl hne

end CFSG.Quasithin.Vol2.Ch11.O10
