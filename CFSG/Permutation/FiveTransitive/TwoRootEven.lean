module

public import CFSG.Permutation.FiveTransitive.CyclePatternRoots
public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG

namespace FiveTransitive.TwoRootEven

open Equiv CyclePatternRoots

variable {X : Type*}

private def twoRootPerm (g : Perm X) : Perm (TwoRoot g) where
  toFun x := ⟨g x.val, ⟨congrArg g x.property.1, g.injective.ne x.property.2⟩⟩
  invFun x := ⟨g x.val, ⟨congrArg g x.property.1, g.injective.ne x.property.2⟩⟩
  left_inv x := Subtype.ext x.property.1
  right_inv x := Subtype.ext x.property.1

theorem even_two_card [Finite X] (g : Perm X) : Even (Nat.card (TwoRoot g)) := by
  classical
  let _ : Fintype (TwoRoot g) := Fintype.ofFinite _
  have hp : twoRootPerm g ^ 2 = 1 := by
    ext x
    exact x.property.1
  have hs : (twoRootPerm g).support = Finset.univ := by
    ext x
    simp only [Perm.mem_support, Finset.mem_univ, iff_true]
    intro h
    exact x.property.2 (congrArg Subtype.val h)
  have hd := Perm.two_dvd_card_support hp
  rw [hs, Finset.card_univ, ← Nat.card_eq_fintype_card] at hd
  exact even_iff_two_dvd.mpr hd

end FiveTransitive.TwoRootEven

end CFSG
