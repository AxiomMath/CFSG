module

public import CFSG.Monster.B.Dyadic.PinnedK

public section

namespace CFSG.Monster.B.Dyadic

@[expose] noncomputable def wordCD (w : List Bool) : Matrix (Fin 4370) (Fin 4370) (ZMod 2) :=
  (w.map fun l => if l then cK else dK).prod

end CFSG.Monster.B.Dyadic

end
