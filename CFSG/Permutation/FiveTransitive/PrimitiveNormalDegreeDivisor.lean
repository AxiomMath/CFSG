module

public import Mathlib.GroupTheory.GroupAction.Primitive

public section

namespace CFSG

namespace FiveTransitive.PrimitiveNormalDegreeDivisor
open MulAction

theorem degree_dvd_card
    {G E : Type*} [Group G] [Finite G] [Finite E] [Nonempty E]
    [MulAction G E] [FaithfulSMul G E] [IsPreprimitive G E]
    (N : Subgroup G) [N.Normal] (hN : N ≠ ⊥) : Nat.card E ∣ Nat.card N := by
  let _ : Nontrivial N := N.nontrivial_iff_ne_bot.mpr hN
  have hnotfixed : fixedPoints N E ≠ Set.univ := by
    intro hfixed
    apply not_subsingleton N
    constructor
    intro a b
    apply Subtype.ext
    apply FaithfulSMul.eq_of_smul_eq_smul (α := E)
    intro x
    have hx : x ∈ fixedPoints N E := hfixed.symm ▸ Set.mem_univ x
    exact (hx a).trans (hx b).symm
  let _ : IsPretransitive N E := IsQuasiPreprimitive.isPretransitive_of_normal hnotfixed
  let x : E := Classical.choice inferInstance
  rw [← index_stabilizer_of_transitive N x]
  exact (stabilizer N x).index_dvd_card

end FiveTransitive.PrimitiveNormalDegreeDivisor

end CFSG
