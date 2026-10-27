module

public import CFSG.Timmesfeld.Exceptional.DeepQData
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.Timmesfeld.Moufang.Deep

@[expose] def ofTab (t : Array ℕ) (x : Fin 162) : Fin 162 :=
  ⟨t[x.val]! % 162, Nat.mod_lt _ (by norm_num)⟩

end CFSG.Timmesfeld.Moufang.Deep
