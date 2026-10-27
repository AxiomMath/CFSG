module

public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.SetLike

public section

namespace CFSG.RankThree.PartTwo.Sec21.Holder214Theta

@[expose] def a8C1 : Equiv.Perm (Fin 8) := Equiv.swap 0 1 * Equiv.swap 1 2

@[expose] def a8C2 : Equiv.Perm (Fin 8) := Equiv.swap 3 4 * Equiv.swap 4 5

@[expose] def a8Tau : Equiv.Perm (Fin 8) := Equiv.swap 6 7

end CFSG.RankThree.PartTwo.Sec21.Holder214Theta
