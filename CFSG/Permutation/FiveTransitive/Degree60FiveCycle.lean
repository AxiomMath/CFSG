module

public import CFSG.Permutation.FiveTransitive.SmallSupportSeven
public import Mathlib.GroupTheory.Perm.Cycle.Concrete
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG

namespace FiveTransitive.Degree60FiveCycle

theorem exists_even_five_cycle
    (X : Type) [Fintype X] [DecidableEq X] (hcard : 5 ≤ Fintype.card X) :
    ∃ g : Equiv.Perm X, g ∈ alternatingGroup X ∧ orderOf g = 5 ∧
      g.support.card = 5 ∧
      Fintype.card (Function.fixedPoints g) = Fintype.card X - 5 := by
  classical
  obtain ⟨e⟩ : Nonempty (Fin 5 ↪ X) := Function.Embedding.nonempty_of_card_le (by simpa using hcard)
  let c : Equiv.Perm (Fin 5) := List.formPerm [0,1,2,3,4]
  let f := Equiv.Perm.viaEmbeddingHom e
  let g := f c
  have hf : Function.Injective f := by
    intro a b h
    apply Equiv.ext
    intro x
    have hh := congrArg (fun t : Equiv.Perm X => t (e x)) h
    exact e.injective (by simpa only [f,Equiv.Perm.viaEmbeddingHom_apply,Equiv.Perm.viaEmbedding_apply] using hh)
  have hc : orderOf c = 5 := by
    have hcyc : c.IsCycle := List.isCycle_formPerm (by decide) (by norm_num)
    rw [hcyc.orderOf]
    decide
  have hg : orderOf g = 5 := (orderOf_injective f hf c).trans hc
  have hsign5 : g.sign ^ 5 = 1 := by rw [← map_pow,← hg,pow_orderOf_eq_one,map_one]
  have hsign : g.sign = 1 := by
    rcases Int.units_eq_one_or g.sign with h | h
    · exact h
    · rw [h] at hsign5
      norm_num at hsign5
  have hs : g.support.card = 5 := by
    change (c.viaEmbedding e).support.card = 5
    rw [SmallSupportSeven.support_card_viaEmbedding]
    decide
  refine ⟨g,Equiv.Perm.mem_alternatingGroup.mpr hsign,hg,hs,?_⟩
  rw [Equiv.Perm.card_fixedPoints,g.sum_cycleType,hs]

end FiveTransitive.Degree60FiveCycle

end CFSG
