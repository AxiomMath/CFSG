module

public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.RankThree.PartTwo.Sec15

theorem eq_one_of_mem_of_odd_orderOf' {X : Type*} [Group X] {P : Subgroup X}
    (hP : IsPGroup 2 P) {x : X} (hx : x ∈ P) (hodd : Odd (orderOf x)) : x = 1 := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hP ⟨x, hx⟩
  rw [Subgroup.orderOf_mk] at hk
  rw [hk] at hodd
  have hk0 : k = 0 := by
    by_contra hne
    exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, hne⟩)
  rw [hk0, pow_zero] at hk
  exact orderOf_eq_one_iff.mp hk

end CFSG.RankThree.PartTwo.Sec15
