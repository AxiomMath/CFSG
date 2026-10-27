module

public import Mathlib.GroupTheory.Perm.Support
public import Mathlib.Data.Set.Card
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.GroupTheory.GroupAction.Defs

public section

namespace CFSG

namespace FiveTransitive.NineOrbitRestriction
open MulAction

theorem fixes_complement
    {E : Type*} [Finite E] (hE : Nat.card E ≤ 10)
    (B : Subgroup (Equiv.Perm E)) (x : E) (hx : Nat.card (orbit B x) = 9)
    (b : B) (y : E) (hy : y ∉ orbit B x) : b • y = y := by
  have hc : ((orbit B x)ᶜ : Set E).ncard ≤ 1 := by
    rw [Set.ncard_compl,← Nat.card_coe_set_eq,hx]
    omega
  have hs : ((orbit B x)ᶜ : Set E).Subsingleton := Set.ncard_le_one_iff_subsingleton.mp hc
  apply hs _ hy
  intro hby
  exact hy (by simpa only [inv_smul_smul] using mem_orbit_of_mem_orbit b⁻¹ hby)

theorem support_le_nine
    {E : Type*} [Fintype E] [DecidableEq E] (hE : Nat.card E ≤ 10)
    (B : Subgroup (Equiv.Perm E)) (x : E) (hx : Nat.card (orbit B x) = 9)
    (b : B) : (b : Equiv.Perm E).support.card ≤ 9 := by
  have hs : ((b : Equiv.Perm E).support : Set E) ⊆ orbit B x := by
    intro y hy
    by_contra hn
    exact (Equiv.Perm.mem_support.mp hy) (fixes_complement hE B x hx b y hn)
  have hb := Set.ncard_le_ncard hs
  rwa [Set.ncard_coe_finset,← Nat.card_coe_set_eq,hx] at hb

end FiveTransitive.NineOrbitRestriction

end CFSG
