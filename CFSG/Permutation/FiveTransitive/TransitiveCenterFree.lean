module

public import CFSG.Permutation.FiveTransitive.FreeActionTransporterCount
public import Mathlib.Algebra.Group.Action.Pretransitive
public import Mathlib.Algebra.Group.Subgroup.Actions

public section

namespace CFSG

namespace FiveTransitive.TransitiveCenterFree

open MulAction

theorem free
    {G X : Type*} [Group G] [MulAction G X] [FaithfulSMul G X]
    (htrans : IsPretransitive G X)
    (c : Subgroup.center G) (x : X) (hc : c • x = x) : c = 1 := by
  apply Subtype.ext
  apply FaithfulSMul.eq_of_smul_eq_smul (α := X)
  intro y
  obtain ⟨g,rfl⟩ := htrans.exists_smul_eq x y
  change c.val • (g • x) = (1 : G) • (g • x)
  rw [one_smul,← mul_smul,← Subgroup.mem_center_iff.mp c.property g,mul_smul]
  exact congrArg (fun z : X => g • z) hc

theorem card_mul_orbits
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]
    (htrans : IsPretransitive G X) :
    Nat.card (Subgroup.center G) * Nat.card (orbitRel.Quotient (Subgroup.center G) X) =
      Nat.card X := by
  have h := FreeActionTransporterCount.card_orbit_preimage
    (free htrans) (fun _ => True)
  simpa only [Nat.card_subtype_true] using h.symm

theorem card_le
    {G X : Type*} [Group G] [Finite G] [Finite X] [Nonempty X]
    [MulAction G X] [FaithfulSMul G X]
    (htrans : IsPretransitive G X) : Nat.card (Subgroup.center G) ≤ Nat.card X := by
  obtain ⟨x⟩ := ‹Nonempty X›
  exact Nat.card_le_card_of_injective (fun c : Subgroup.center G => c • x)
    (FreeActionTransporterCount.smul_injective (free htrans) x)

end FiveTransitive.TransitiveCenterFree

end CFSG
