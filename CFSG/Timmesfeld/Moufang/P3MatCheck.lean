module

public import CFSG.Timmesfeld.Moufang.P3Mat
public import CFSG.Timmesfeld.Moufang.J2Mat

public section

namespace CFSG.Timmesfeld.Moufang.P3

open CFSG.Sporadic.Bridge.J2 (idL lwordL mA mB)
open CFSG.Timmesfeld.Moufang.J2 (genL)

@[expose] def codes5 (w : List (Fin 5 × Bool)) : List (ℕ × Bool) := w.map fun l => (l.1.val, l.2)

theorem lwordL_wordA : lwordL genL genL (codes5 wordA) idL = mA := by
  decide +kernel

theorem lwordL_wordB : lwordL genL genL (codes5 wordB) idL = mB := by
  decide +kernel

theorem lwordL_conjX3 :
    lwordL genL genL (codes5 conjX3 ++ [(0, true)]) idL =
      lwordL genL genL ((5, true) :: codes5 conjX3) idL := by
  decide +kernel

theorem lwordL_conjX4 :
    lwordL genL genL (codes5 conjX4 ++ [(0, true)]) idL =
      lwordL genL genL ((6, true) :: codes5 conjX4) idL := by
  decide +kernel

end CFSG.Timmesfeld.Moufang.P3
