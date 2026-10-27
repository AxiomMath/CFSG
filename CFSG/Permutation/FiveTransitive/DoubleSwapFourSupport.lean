module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG

namespace FiveTransitive.DoubleSwapFourSupport

theorem exists_even_involution
    (X : Type*) [Fintype X] [DecidableEq X] (hcard : 4 ≤ Fintype.card X) :
    ∃ g : Equiv.Perm X, g ∈ alternatingGroup X ∧ orderOf g = 2 ∧
      g.support.card = 4 ∧
      Fintype.card (Function.fixedPoints g) = Fintype.card X - 4 := by
  obtain ⟨e⟩ : Nonempty (Fin 4 ↪ X) := Function.Embedding.nonempty_of_card_le (by simpa using hcard)
  have hd : ([0, 1, 2, 3] : List (Fin 4)).Nodup := by decide
  have he : [e 0, e 1, e 2, e 3].Nodup := by
    simpa only [List.map_cons, List.map_nil] using hd.map e.injective
  let g : Equiv.Perm X := Equiv.swap (e 0) (e 1) * Equiv.swap (e 2) (e 3)
  have ht : g.cycleType = {2, 2} := Equiv.Perm.cycleType_swap_mul_swap_of_nodup he
  have h01 : e 0 ≠ e 1 := e.injective.ne (by decide)
  have h23 : e 2 ≠ e 3 := e.injective.ne (by decide)
  have hsign : g.sign = 1 := by
    change (Equiv.swap (e 0) (e 1) * Equiv.swap (e 2) (e 3)).sign = 1
    rw [map_mul, Equiv.Perm.sign_swap h01, Equiv.Perm.sign_swap h23]
    simp
  refine ⟨g, Equiv.Perm.mem_alternatingGroup.mpr hsign, ?_, ?_, ?_⟩
  · rw [← g.lcm_cycleType, ht]
    decide
  · rw [← g.sum_cycleType, ht]
    decide
  · rw [g.card_fixedPoints, ht]
    rfl

end FiveTransitive.DoubleSwapFourSupport

end CFSG
