module

public import Mathlib.Algebra.Group.Subgroup.Ker

public section

namespace CFSG.Quasithin.Background.Harris.OrdinaryProofs

variable {G C : Type*} [Group G] [Group C]

theorem maximal_of_comap_maximal {Ψ : G →* C} {B : Subgroup C} (hB : Ψ.range = B)
    {U : Subgroup C} (hmax : ∀ H : Subgroup G, U.comap Ψ ≤ H → H = U.comap Ψ ∨ H = ⊤) :
    ∀ V : Subgroup C, U ≤ V → V ≤ B → V = U ∨ V = B := by
  intro V hUV hVB
  rcases hmax (V.comap Ψ) (fun g hg => hUV (Subgroup.mem_comap.mp hg)) with h | h
  · left
    refine le_antisymm (fun c hc => ?_) hUV
    have hcB : c ∈ B := hVB hc
    rw [← hB, MonoidHom.mem_range] at hcB
    obtain ⟨g, rfl⟩ := hcB
    have hg : g ∈ V.comap Ψ := Subgroup.mem_comap.mpr hc
    rw [h] at hg
    exact Subgroup.mem_comap.mp hg
  · right
    refine le_antisymm hVB (fun c hc => ?_)
    rw [← hB, MonoidHom.mem_range] at hc
    obtain ⟨g, rfl⟩ := hc
    have hg : g ∈ V.comap Ψ := by rw [h]; exact Subgroup.mem_top g
    exact Subgroup.mem_comap.mp hg

end CFSG.Quasithin.Background.Harris.OrdinaryProofs

end
