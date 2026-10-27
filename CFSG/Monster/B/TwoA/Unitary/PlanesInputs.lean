module

public import CFSG.Monster.B.TwoA.Unitary.Form
public meta import CFSG.Monster.B.TwoA.Unitary.Form
import CFSG.Fischer.F4
public meta import Mathlib
public import Mathlib

public section

namespace CFSG.Monster.B.TwoA.Unitary

open CFSG.Fischer Matrix
open CFSG.Monster.B.Classical.UnitarySix (bar bar_add bar_mul bar_bar bar_zero bar_one
  bar_eq_zero_iff)

@[expose] def piv (v : V6) : Fin 6 := ((List.finRange 6).find? fun i => v i ≠ 0).getD 0

@[expose] def rrefOK (j : Fin 891) : Prop :=
  ∀ a b : Fin 3, planeRow j a (piv (planeRow j b)) = if a = b then 1 else 0

@[expose] def expand (j : Fin 891) (x : V6) : V6 :=
  ∑ b : Fin 3, x (piv (planeRow j b)) • planeRow j b

@[expose] def imgRow (k : Fin 17) (j : Fin 891) (a : Fin 3) : V6 :=
  b6Map k (planeRow (b6Iso j) a)

end CFSG.Monster.B.TwoA.Unitary
