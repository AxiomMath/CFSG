module

public import Mathlib.GroupTheory.GroupAction.Jordan

public section

namespace CFSG

namespace FiveTransitive.LargePrimeCyclePrimitive
open MulAction

theorem isPreprimitive
    {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) [IsPretransitive P X]
    {g : Equiv.Perm X} (hg : g ∈ P) (hc : g.IsCycle)
    (hp : g.support.card.Prime) (hlarge : Nat.card X < 2 * g.support.card) :
    IsPreprimitive P X := by
  classical
  let s : Set X := (g.support : Set X)ᶜ
  let H := fixingSubgroup P s
  let Y := SubMulAction.ofFixingSubgroup P s
  let : IsPretransitive H Y := Equiv.Perm.isPretransitive_of_isCycle_mem hc hg
  have hY : Nat.card Y = g.support.card := by
    change Nat.card (SubMulAction.ofFixingSubgroup P ((g.support : Set X)ᶜ)) = _
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext x
    simp [SubMulAction.mem_ofFixingSubgroup_iff]
  let : IsPreprimitive H Y := IsPreprimitive.of_prime_card (hY.symm ▸ hp)
  let f : Y →ₑ[H.subtype] X :=
    { toFun := Subtype.val
      map_smul' := fun _ _ => rfl }
  apply IsPreprimitive.of_card_lt (f := f)
  rw [Set.ncard_range_of_injective (show Function.Injective f from Subtype.val_injective)]
  simpa only [hY] using hlarge

end FiveTransitive.LargePrimeCyclePrimitive

end CFSG
