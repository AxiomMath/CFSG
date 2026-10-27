module

public import CFSG.RankThree.GF2n.Stroth80.Sec7FormsProportional
public import CFSG.RankThree.GF2n.Stroth80.Sec7MapProportional

public section

namespace CFSG.RankThree.GF2n.Stroth80

theorem sec7_maps_proportional_of_perp_agree {K E : Type*} [Field K] [Finite K]
    [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    (f : LinearMap.BilinForm K E) (hf : f.Nondegenerate) (hr : f.IsRefl)
    (U : Submodule K E) (hU : Module.finrank K U = 4) (ψ ψ' : E →ₗ[K] E)
    (hr1 : LinearMap.range ψ = U) (hr2 : LinearMap.range ψ' = U)
    (hk2 : LinearMap.ker ψ' = f.orthogonal U)
    (β₁ β₂ : LinearMap.BilinForm K U)
    (hβ₁ : ∀ (x y : U) (c : E), ψ c = (y : E) → β₁ x y = f x c)
    (hβ₂ : ∀ (x y : U) (c : E), ψ' c = (y : E) → β₂ x y = f x c)
    (h₁ : β₁.Nondegenerate) (h₂ : β₂.Nondegenerate)
    (O : Set (Submodule K U)) (hO1 : ∀ P ∈ O, Module.finrank K P = 1)
    (hcard : O.ncard = Nat.card K ^ 2 + 1)
    (hline : ∀ l : Submodule K U, Module.finrank K l = 2 → {P | P ∈ O ∧ P ≤ l}.ncard ≤ 2)
    (hplane : ∀ π : Submodule K U, Module.finrank K π = 3 →
      {P | P ∈ O ∧ P ≤ π}.ncard ≤ Nat.card K + 1)
    (hperp : ∀ P ∈ O, ∀ x ∈ P, ∀ y, β₂ x y = 0 ↔ β₁ x y = 0) :
    ∃ μ : K, μ ≠ 0 ∧ ∀ c : E, ψ c = μ • ψ' c := by
  obtain ⟨μ, hμ0, hμ⟩ := sec7_forms_proportional hU β₁ β₂ h₁ h₂ O hO1 hcard hline hplane hperp
  refine ⟨μ, hμ0, ?_⟩
  refine sec7_map_eq_smul_of_form_eq f hf hr U ψ ψ' hr1 hr2 hk2 μ hμ0 ?_
  intro x hx c c' hc'
  have hψc : ψ c ∈ U := hr1 ▸ LinearMap.mem_range_self ψ c
  have h1 := hβ₂ ⟨x, hx⟩ ⟨ψ c, hψc⟩ c' hc'
  have h2 := hβ₁ ⟨x, hx⟩ ⟨ψ c, hψc⟩ c rfl
  have h3 := hμ ⟨x, hx⟩ ⟨ψ c, hψc⟩
  rw [← h1, h3, h2]

end CFSG.RankThree.GF2n.Stroth80
