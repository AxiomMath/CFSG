module

public import CFSG.Quasithin.Background.JonesParshallWords

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Quasithin.JonesParshall

section Fox

variable {G : Type*} [Group G] {M : Type*} [AddCommGroup M]

theorem Z1A_le_B1A_of_fox (μ : G →* AddMonoid.End M) {gens : Fin 2 → G}
    {rels : List (List (Fin 2))} (hgen : Subgroup.closure (Set.range gens) = ⊤)
    (hrels : ∀ r ∈ rels, wordEval gens r = 1)
    (hsol : ∀ v₀ v₁ : M, (∀ r ∈ rels, foxEval μ gens ![v₀, v₁] r = 0) →
      ∃ m, v₀ = μ (gens 0) m - m ∧ v₁ = μ (gens 1) m - m) : Z1A μ ≤ B1A μ := by
  intro f hf
  have hrel : ∀ r ∈ rels, foxEval μ gens ![f (gens 0), f (gens 1)] r = 0 := by
    intro r hr
    have h := Z1A_wordEval hf gens r
    rw [hrels r hr, Z1A_one hf] at h
    have hv : (![f (gens 0), f (gens 1)] : Fin 2 → M) = fun i => f (gens i) := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    exact h.symm
  obtain ⟨m, h0, h1⟩ := hsol _ _ hrel
  have hf' : f - coboundaryA μ m ∈ Z1A μ := sub_mem hf (B1A_le_Z1A μ ⟨m, rfl⟩)
  have hz := eq_zero_of_vanish_closure hf' hgen (by
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · show f (gens 0) - (μ (gens 0) m - m) = 0
      rw [← h0]
      exact sub_self _
    · show f (gens 1) - (μ (gens 1) m - m) = 0
      rw [← h1]
      exact sub_self _)
  exact ⟨m, (sub_eq_zero.1 hz).symm⟩

end Fox

end FFC

end CFSG.Quasithin
