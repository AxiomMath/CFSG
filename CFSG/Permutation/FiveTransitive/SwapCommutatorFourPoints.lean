module

public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG

open scoped commutatorElement

namespace FiveTransitive.SwapCommutatorFourPoints

theorem shape
    {F : Type*} [Fintype F] [DecidableEq F] (e : Fin 4 ↪ F) :
    let d := Equiv.swap (e 0) (e 1) * Equiv.swap (e 2) (e 3)
    orderOf d = 2 ∧ d.support.card = 4 ∧
      Nat.card (Function.fixedPoints d) = Nat.card F - 4 := by
  have hd : ([0, 1, 2, 3] : List (Fin 4)).Nodup := by decide
  have he : [e 0, e 1, e 2, e 3].Nodup := by
    simpa only [List.map_cons, List.map_nil] using hd.map e.injective
  let d := Equiv.swap (e 0) (e 1) * Equiv.swap (e 2) (e 3)
  have ht : d.cycleType = {2, 2} := Equiv.Perm.cycleType_swap_mul_swap_of_nodup he
  refine ⟨?_, ?_, ?_⟩
  · rw [← d.lcm_cycleType, ht]
    decide
  · rw [← d.sum_cycleType, ht]
    decide
  · rw [Nat.card_eq_fintype_card, d.card_fixedPoints, ht, Nat.card_eq_fintype_card]
    rfl

end FiveTransitive.SwapCommutatorFourPoints

end CFSG
