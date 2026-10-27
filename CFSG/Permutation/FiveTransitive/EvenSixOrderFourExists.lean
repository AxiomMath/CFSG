module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG

namespace FiveTransitive.EvenSixOrderFourExists

open Equiv

private theorem exists_even_order_four
    (X : Type*) [Fintype X] [DecidableEq X] (hX : Fintype.card X = 6) :
    ∃ a : Perm X, a.sign = 1 ∧ orderOf a = 4 := by
  let g : Perm (Fin 6) := swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5
  have hg : g.sign = 1 ∧ g ^ 4 = 1 ∧ g ^ 2 ≠ 1 := by decide +kernel
  have horder : orderOf g = 4 := orderOf_eq_prime_pow (p := 2) (n := 1) hg.2.2 hg.2.1
  let e := Fintype.equivFinOfCardEq hX
  let f := e.symm.permCongrHom
  refine ⟨f g, ?_, ?_⟩
  · exact (Perm.sign_permCongr e.symm g).trans hg.1
  · exact (orderOf_injective f.toMonoidHom f.injective g).trans horder

theorem exists_order_four_of_alternating_image
    (G X : Type*) [Group G] [Finite G] [Fintype X] [DecidableEq X]
    (f : G →* Perm X) (hX : Fintype.card X = 6) (hf : f.range = alternatingGroup X) :
    ∃ a : G, orderOf a = 4 := by
  obtain ⟨g, hsign, hg⟩ := exists_even_order_four X hX
  have hmem : g ∈ f.range := by rw [hf]; exact Perm.mem_alternatingGroup.mpr hsign
  obtain ⟨b, hb⟩ := hmem
  have hd : 4 ∣ orderOf b := by
    rw [← hg, ← hb]
    exact orderOf_map_dvd f b
  exact ⟨b ^ (orderOf b / 4), orderOf_pow_orderOf_div (ne_of_gt (orderOf_pos b)) hd⟩

end FiveTransitive.EvenSixOrderFourExists

end CFSG
