module

public import CFSG.LieType.Chevalley.KernelComponentRoots

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

variable {τ : Tag}

theorem exists_pair_ne_of_two_le_finrank_span
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    (h2 : 2 ≤ Module.finrank ℤ (Submodule.span ℤ Ψ)) :
    ∃ α ∈ Ψ, ∃ β ∈ Ψ, β ≠ α ∧ β ≠ -α ∧ iform α β ≠ 0 := by
  have hne : Ψ.Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    subst hempty
    rw [Submodule.span_empty, finrank_bot] at h2
    omega
  obtain ⟨α, hα⟩ := hne
  by_contra hcon
  push Not at hcon
  have hsub : ({α, -α} : Set (Fin τ.rank → ℤ)) ⊆ Ψ := by
    intro a ha
    rcases ha with rfl | rfl
    · exact hα
    · exact hΨ.neg_mem _ hα
  have horth : ∀ a ∈ ({α, -α} : Set (Fin τ.rank → ℤ)), ∀ b ∈ Ψ,
      b ∉ ({α, -α} : Set (Fin τ.rank → ℤ)) → iform a b = 0 := by
    intro a ha b hb hbS
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hbS
    have h0 : iform α b = 0 := hcon α hα b hb hbS.1 hbS.2
    rcases ha with rfl | rfl
    · exact h0
    · rw [← neg_one_smul ℤ α, iform_smul_left, h0, mul_zero]
  rcases hΨ.irreducible _ hsub horth with h | h
  · exact absurd h (Set.insert_nonempty _ _).ne_empty
  · rw [← h] at h2
    have hle : Module.finrank ℤ (Submodule.span ℤ ({α, -α} : Set (Fin τ.rank → ℤ))) ≤ 1 := by
      have h1 : Submodule.span ℤ ({α, -α} : Set (Fin τ.rank → ℤ)) ≤
          Submodule.span ℤ ({α} : Set (Fin τ.rank → ℤ)) := by
        rw [Submodule.span_le]
        intro a ha
        rcases ha with rfl | rfl
        · exact Submodule.subset_span rfl
        · exact Submodule.neg_mem _ (Submodule.subset_span rfl)
      calc Module.finrank ℤ (Submodule.span ℤ ({α, -α} : Set (Fin τ.rank → ℤ)))
          ≤ Module.finrank ℤ (Submodule.span ℤ ({α} : Set (Fin τ.rank → ℤ))) :=
            Submodule.finrank_mono h1
        _ ≤ 1 := by simpa using finrank_span_le_card ({α} : Set (Fin τ.rank → ℤ))
    omega

end CFSG.StandardType.TableCRes
