module

public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.GroupAction.Defs

public section

namespace CFSG

namespace FiveTransitive.OrbitFixedComplementBound

open MulAction

theorem card_le
    {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (x : X) : Nat.card (orbit G x) ≤ max 1 (Nat.card X - Nat.card (fixedPoints G X)) := by
  by_cases hx : x ∈ fixedPoints G X
  · have he : orbit G x = {x} := by
      ext y
      constructor
      · rintro ⟨g,rfl⟩
        exact hx g
      · intro hy
        have hyx : y = x := hy
        subst y
        exact mem_orbit_self x
    rw [he,Nat.card_coe_set_eq,Set.ncard_singleton]
    exact le_max_left _ _
  · have hsub : orbit G x ⊆ (fixedPoints G X)ᶜ := by
      rintro y ⟨g,rfl⟩ hy
      have he : g • x = x := by
        simpa only [inv_smul_smul] using (hy g⁻¹).symm
      exact hx (he ▸ hy)
    have hb := Set.ncard_le_ncard hsub
    rw [← Nat.card_coe_set_eq,Set.ncard_compl,← Nat.card_coe_set_eq] at hb
    exact hb.trans (le_max_right _ _)

end FiveTransitive.OrbitFixedComplementBound

end CFSG
