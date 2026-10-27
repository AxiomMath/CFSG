module

public import CFSG.Timmesfeld.Exceptional.DeepHData

public section

namespace CFSG.Timmesfeld.Moufang.Deep

@[expose] def tD : Fin 4 → Bool := ![true, false, true, false]

@[expose] def wJ (i : Fin 4) (k : Fin 3) : List (Fin 7 × Bool) :=
  (if tD i then [(0, true)] else []) ++ [(⟨k.val + 4, by omega⟩, true)] ++
    (tZ i).map fun l => (Fin.castLE (by norm_num) l.1, l.2)

end CFSG.Timmesfeld.Moufang.Deep
