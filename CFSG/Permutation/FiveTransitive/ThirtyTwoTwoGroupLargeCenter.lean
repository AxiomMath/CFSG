module

public import CFSG.Permutation.FiveTransitive.TransitiveCenterFree
public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG

namespace FiveTransitive.ThirtyTwoTwoGroupLargeCenter

open MulAction

private theorem free_of_min_support
    {X : Type*} [Fintype X] [DecidableEq X] (hX : Nat.card X = 32)
    (R : Subgroup (Equiv.Perm X)) (htrans : IsPretransitive R X)
    (hZ : 16 ≤ Nat.card (Subgroup.center R))
    (K : Subgroup (Equiv.Perm X)) (hKR : K ≤ R)
    (hmin : ∀ k : K, k ≠ 1 → 27 ≤ k.val.support.card) :
    ∀ (k : K) (x : X), k • x = x → k = 1 := by
  intro k x hx
  by_contra hk
  let Z := Subgroup.center R
  let r : R := ⟨k.val,hKR k.property⟩
  have hfix (c : Z) : k.val (c • x) = c • x := by
    have hc := Subgroup.mem_center_iff.mp c.property r
    have he := congrArg (fun a : R => a.val x) hc
    change k.val (c • x) = c • (k.val x) at he
    exact he.trans (congrArg (fun y : X => c • y) hx)
  let f : Z → Function.fixedPoints k.val := fun c => ⟨c • x,hfix c⟩
  have hf : Function.Injective f := by
    intro a b he
    exact FreeActionTransporterCount.smul_injective (TransitiveCenterFree.free htrans) x
      (congrArg Subtype.val he)
  have hb := Nat.card_le_card_of_injective f hf
  change Nat.card (Subgroup.center R) ≤ Nat.card (Function.fixedPoints k.val) at hb
  rw [Nat.card_eq_fintype_card (α := Function.fixedPoints k.val),Equiv.Perm.card_fixedPoints,k.val.sum_cycleType,
    ← Nat.card_eq_fintype_card (α := X),hX] at hb
  have hm := hmin k hk
  have hle : k.val.support.card ≤ 32 := by
    have hh := Finset.card_le_univ k.val.support
    rwa [← Nat.card_eq_fintype_card,hX] at hh
  omega

theorem card_le_thirty_two
    {X : Type*} [Fintype X] [DecidableEq X] (hX : Nat.card X = 32)
    (R : Subgroup (Equiv.Perm X)) (htrans : IsPretransitive R X)
    (hZ : 16 ≤ Nat.card (Subgroup.center R))
    (K : Subgroup (Equiv.Perm X)) (hKR : K ≤ R)
    (hmin : ∀ k : K, k ≠ 1 → 27 ≤ k.val.support.card) : Nat.card K ≤ 32 := by
  have hn : Nonempty X := Finite.card_pos_iff.mp (by omega)
  obtain ⟨x⟩ := hn
  have hb := Nat.card_le_card_of_injective (fun k : K => k • x)
    (FreeActionTransporterCount.smul_injective (free_of_min_support hX R htrans hZ K hKR hmin) x)
  rwa [hX] at hb

end FiveTransitive.ThirtyTwoTwoGroupLargeCenter

end CFSG
