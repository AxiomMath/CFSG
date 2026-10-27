module

public import Mathlib.Data.Finite.Perm
public import Mathlib.GroupTheory.Abelianization.Defs

public section

namespace CFSG

namespace FiveTransitive.TwoPointActionCommutator

theorem apply_eq_one
    {G Y : Type*} [Group G] [Finite Y]
    (f : G →* Equiv.Perm Y) (hcard : Nat.card Y ≤ 2)
    (a : G) (ha : a ∈ commutator G) : f a = 1 := by
  have hc : IsMulCommutative (Equiv.Perm Y) :=
    Equiv.Perm.isMulCommutative_iff_card_le_two.mpr hcard
  letI : CommGroup (Equiv.Perm Y) :=
    { Equiv.Perm.permGroup with mul_comm := isMulCommutative_iff.mp hc }
  exact Abelianization.commutator_subset_ker f ha

end FiveTransitive.TwoPointActionCommutator

end CFSG
