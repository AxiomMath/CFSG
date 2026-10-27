module

public import CFSG.Sporadic.Recognition.McLMultiplierInputs
public import CFSG.Sporadic.McL.Setup

public section

namespace CFSG.Sporadic.Recognition.McLMultiplier

open CFSG.Sporadic.McL

@[expose] noncomputable def mclLetY (z : ℤ) : Matrix (Fin 21) (Fin 21) (ZMod 3) :=
  if z = 1 ∨ z = -1 then mA else if z = 2 then mB else mB ^ 4

@[expose] noncomputable def mclY (k : ℕ) : Matrix (Fin 21) (Fin 21) (ZMod 3) :=
  ((mclGenWord k).map mclLetY).prod

@[expose] noncomputable def mclEvalY (w : List (Fin 6 × Bool)) : Matrix (Fin 21) (Fin 21) (ZMod 3) :=
  (w.map fun l => mclY l.1.val).prod

end CFSG.Sporadic.Recognition.McLMultiplier

end
