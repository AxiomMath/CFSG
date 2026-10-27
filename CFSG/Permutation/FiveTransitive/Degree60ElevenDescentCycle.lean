module

public import CFSG.Permutation.FiveTransitive.SmallSupportSeven
public import Mathlib.GroupTheory.Perm.Cycle.Concrete
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG

namespace FiveTransitive.Degree60ElevenDescentCycle

theorem exists_even_eleven_cycle
    (X : Type) [Fintype X] [DecidableEq X] (hcard : 11 ≤ Fintype.card X) :
    ∃ g : Equiv.Perm X, g ∈ alternatingGroup X ∧ orderOf g = 11 ∧
      g.support.card = 11 ∧
      Fintype.card (Function.fixedPoints g) = Fintype.card X - 11 := by
  classical
  obtain ⟨e⟩ : Nonempty (Fin 11 ↪ X) := Function.Embedding.nonempty_of_card_le (by simpa using hcard)
  let c : Equiv.Perm (Fin 11) := List.formPerm [0,1,2,3,4,5,6,7,8,9,10]
  let f := Equiv.Perm.viaEmbeddingHom e
  let g := f c
  have hf : Function.Injective f := by
    intro a b h
    apply Equiv.ext
    intro x
    have hh := congrArg (fun t : Equiv.Perm X => t (e x)) h
    exact e.injective (by simpa only [f,Equiv.Perm.viaEmbeddingHom_apply,Equiv.Perm.viaEmbedding_apply] using hh)
  have hc : orderOf c = 11 := by
    have hcyc : c.IsCycle := List.isCycle_formPerm (by decide) (by norm_num)
    rw [hcyc.orderOf]
    decide
  have hg : orderOf g = 11 := (orderOf_injective f hf c).trans hc
  have hsign5 : g.sign ^ 11 = 1 := by rw [← map_pow,← hg,pow_orderOf_eq_one,map_one]
  have hsign : g.sign = 1 := by
    rcases Int.units_eq_one_or g.sign with h | h
    · exact h
    · rw [h] at hsign5
      norm_num at hsign5
  have hs : g.support.card = 11 := by
    change (c.viaEmbedding e).support.card = 11
    rw [SmallSupportSeven.support_card_viaEmbedding]
    decide
  refine ⟨g,Equiv.Perm.mem_alternatingGroup.mpr hsign,hg,hs,?_⟩
  rw [Equiv.Perm.card_fixedPoints,g.sum_cycleType,hs]

end FiveTransitive.Degree60ElevenDescentCycle

end CFSG
