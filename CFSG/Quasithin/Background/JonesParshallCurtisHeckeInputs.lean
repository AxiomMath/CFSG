module

public import CFSG.Quasithin.Background.JonesParshallCurtisGroupInputs
public import CFSG.Quasithin.Background.JonesParshallCurtisWeylInputs

public section

namespace CFSG.Quasithin.JonesParshall.Curtis

open Matrix

@[expose] def rootB : Bool × Fin 4 → BM
  | (true, s) => xB s
  | (false, s) => yB s

@[expose] def rootBM (l : List (Bool × Fin 4)) : BM := l.foldr (fun a M => bmul (rootB a) M) bone

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G5 V)

end CFSG.Quasithin.JonesParshall.Curtis
