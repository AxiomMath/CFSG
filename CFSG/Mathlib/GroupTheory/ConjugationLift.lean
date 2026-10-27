module

public import Mathlib.GroupTheory.Subgroup.Centralizer

public section

namespace MonoidHom

theorem injective_comp_range_subtype_of_ker_lift
    {H G : Type*} [Group H] [Group G] (ψ : H →* G) (B : Subgroup G)
    (ℓ : B →* H)
    (hℓ : ∀ (b : B) (u : H),
      (b : G)⁻¹ * ψ u * (b : G) = ψ (ℓ b * u * (ℓ b)⁻¹))
    (hker : ℓ.ker.map B.subtype = B ⊓ Subgroup.centralizer (ψ.range : Set G)) :
    Function.Injective (ψ.comp ℓ.range.subtype) := by
  apply (MonoidHom.ker_eq_bot_iff (ψ.comp ℓ.range.subtype)).mp
  rw [eq_bot_iff]
  intro a ha
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  change ψ (a : H) = 1 at ha
  obtain ⟨b, hb⟩ := a.property
  have hψb : ψ (ℓ b) = 1 := (congrArg ψ hb).trans ha
  have hbC : (b : G) ∈ Subgroup.centralizer (ψ.range : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨u, rfl⟩
    have hc := hℓ b u
    simp only [map_mul, map_inv, hψb, one_mul, inv_one, mul_one] at hc
    have h := congrArg (fun z : G => (b : G) * z) hc
    simpa only [mul_assoc, mul_inv_cancel_left] using h
  have hbker : b ∈ ℓ.ker := by
    have hbm : (b : G) ∈ ℓ.ker.map B.subtype := by
      rw [hker]
      exact ⟨b.property, hbC⟩
    obtain ⟨c, hc, hcb⟩ := Subgroup.mem_map.mp hbm
    have hcb' : c = b := Subtype.ext hcb
    exact hcb' ▸ hc
  exact hb.symm.trans (MonoidHom.mem_ker.mp hbker)

end MonoidHom

end
