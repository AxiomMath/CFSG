module

public import CFSG.Permutation.FiveTransitive.EvenSixSylowDihedral

public section

namespace CFSG

namespace FiveTransitive.EvenSixSylowCenter

private theorem dihedral_center : ∀ a x : DihedralGroup 4, a ^ 2 ≠ 1 →
    (∀ y : DihedralGroup 4, x * y = y * x) → x = 1 ∨ x = a ^ 2 := by
  decide +kernel

theorem eq_one_or_square
    (X : Type*) [Fintype X] [DecidableEq X] (hX : Fintype.card X = 6)
    (P : Sylow 2 (alternatingGroup X)) (a x : P) (ha : orderOf a = 4)
    (hx : ∀ y : P, x * y = y * x) : x = 1 ∨ x = a ^ 2 := by
  obtain ⟨e⟩ := EvenSixSylowDihedral.nonempty_equiv_dihedral X hX P
  have hne : (e a) ^ 2 ≠ 1 := by
    intro h
    have hd := orderOf_dvd_of_pow_eq_one h
    have hea : orderOf (e a) = 4 := (orderOf_injective e.toMonoidHom e.injective a).trans ha
    rw [hea] at hd
    norm_num at hd
  have hcentral (y : DihedralGroup 4) : e x * y = y * e x := by
    obtain ⟨z, rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e (hx z)
  rcases dihedral_center (e a) (e x) hne hcentral with h | h
  · left
    apply e.injective
    simpa only [map_one] using h
  · right
    apply e.injective
    simpa only [map_pow] using h

end FiveTransitive.EvenSixSylowCenter

end CFSG
