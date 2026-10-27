module

public import CFSG.Quasithin.EmptyFaithful.S152O4Facts
public import CFSG.Quasithin.EmptyFaithful.S151Statements

public section

namespace CFSG.Quasithin

namespace Y15111

open CFSG.Open S152O4

theorem model_free_three : ∀ τ : Gam, τ ≠ 1 → τ ^ 2 = 1 →
    ∃ α : Gam, α ^ 3 = 1 ∧ α ≠ 1 ∧ (∀ v : Vec, v ≠ 1 → act α v ≠ v) ∧
      τ * α * τ⁻¹ = α⁻¹ := by
  decide +kernel

theorem model_free_normal : ∀ α : Gam, α ^ 3 = 1 → α ≠ 1 → (∀ v : Vec, v ≠ 1 → act α v ≠ v) →
    ∀ g : Gam, g * α * g⁻¹ = α ∨ g * α * g⁻¹ = α⁻¹ := by
  decide +kernel

variable {V : Type} [CommGroup V]

theorem om4_free_three [Finite V] {X : Subgroup (MulAut V)} (hX : IsOmegaFourPlus X)
    {τ : MulAut V} (hτX : τ ∈ X) (hτ1 : τ ≠ 1) (hτ2 : τ ^ 2 = 1) :
    ∃ α ∈ X, α ^ 3 = 1 ∧ α ≠ 1 ∧ (∀ v : V, v ≠ 1 → α v ≠ v) ∧ τ * α * τ⁻¹ = α⁻¹ ∧
      ∀ g ∈ X, g * α * g⁻¹ = α ∨ g * α * g⁻¹ = α⁻¹ := by
  obtain ⟨c, hc⟩ := om4_model hX
  obtain ⟨γ, rfl⟩ := exists_rhoV_eq c hc hτX
  have hγ1 : γ ≠ 1 := fun h => hτ1 (by rw [h, map_one])
  have hγ2 : γ ^ 2 = 1 := rhoV_injective c (by rw [map_pow, map_one]; exact hτ2)
  obtain ⟨a, ha3, ha1, hfree, hinv⟩ := model_free_three γ hγ1 hγ2
  have hfree' : ∀ v : V, v ≠ 1 → rhoV c a v ≠ v := by
    intro v hv h
    refine hfree (c v) (fun h1 => hv (c.injective (by rw [h1, map_one]))) ?_
    rw [← rhoV_apply_of, h]
  refine ⟨rhoV c a, rhoV_mem c hc a, ?_, ?_, hfree', ?_, ?_⟩
  · rw [← map_pow, ha3, map_one]
  · exact fun h => ha1 (rhoV_injective c (by rw [h, map_one]))
  · rw [← map_inv, ← map_mul, ← map_mul, hinv, map_inv]
  · intro g hg
    obtain ⟨δ, rfl⟩ := exists_rhoV_eq c hc hg
    rcases model_free_normal a ha3 ha1 hfree δ with h | h
    · left
      rw [← map_inv, ← map_mul, ← map_mul, h]
    · right
      rw [← map_inv, ← map_mul, ← map_mul, h, map_inv]

variable {G : Type} [Group G] [Finite G]

theorem om4_free_three_on {M V : Subgroup G} (hOm : IsOmegaFourPlusOn M V)
    {τ : MulAut V} (hτM : τ ∈ autOn M V) (hτ1 : τ ≠ 1) (hτ2 : τ ^ 2 = 1) :
    ∃ α ∈ autOn M V, α ^ 3 = 1 ∧ α ≠ 1 ∧ (∀ v : V, v ≠ 1 → α v ≠ v) ∧ τ * α * τ⁻¹ = α⁻¹ ∧
      ∀ g ∈ autOn M V, g * α * g⁻¹ = α ∨ g * α * g⁻¹ = α⁻¹ := by
  obtain ⟨hV, hX⟩ := hOm
  exact om4_free_three (V := IntMod V hV) hX hτM hτ1 hτ2

end Y15111

end CFSG.Quasithin
