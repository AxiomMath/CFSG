module

public import CFSG.Quasithin.AppendixH.H9.H92.Rank6.ElementaryAbelianPerm
public import Std.Tactic.BVDecide.Normalize.Prop

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

theorem card_le_eight_of_isElemAb2 (E : Subgroup (Equiv.Perm (Fin 6))) (hE : IsElemAb2 E) :
    Nat.card E ≤ 8 := by
  have h := PermElemAb2.card_le_two_pow_half 6 Set.univ (by simp) E hE (by simp)
  simpa using h

end CFSG.ASVolI.ChH
