module

public import CFSG.Quasithin.H13.VolIAltCoverSevenData

public section

namespace CFSG.Quasithin.H13.VolI

open CFSG.Quasithin Equiv

@[expose] def a7reps6 : List ↥(alternatingGroup (Fin 7)) :=
  [1, a7c234, a7c234 * a7c234, a7c012 * a7c234, a7c012 * a7c012 * a7c234, a7s * a7s * a7c234]

theorem a7reps6_fix : ∀ h ∈ a7reps6, (h : Perm (Fin 7)) 6 = 6 := by
  intro h hh
  simp only [a7reps6, List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem alt7_cosets6 : ∀ σ : ↥(alternatingGroup (Fin 7)), (σ : Perm (Fin 7)) 6 = 6 ∨
    ∃ h ∈ a7reps6, (((h * a7c456)⁻¹ * σ : ↥(alternatingGroup (Fin 7))) : Perm (Fin 7)) 6 = 6 := by
  intro σ
  have hv : ∀ v : Fin 7, v ≠ 6 → ∃ h ∈ a7reps6,
      ((h * a7c456 : ↥(alternatingGroup (Fin 7))) : Perm (Fin 7)) 6 = v := by
    decide +kernel
  by_cases h6 : (σ : Perm (Fin 7)) 6 = 6
  · exact Or.inl h6
  · obtain ⟨h, hh, he⟩ := hv _ h6
    refine Or.inr ⟨h, hh, ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Perm.mul_apply, Perm.inv_eq_iff_eq, he]

end CFSG.Quasithin.H13.VolI
