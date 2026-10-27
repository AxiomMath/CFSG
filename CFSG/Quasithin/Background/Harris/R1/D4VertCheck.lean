module

public import CFSG.LargeExtraspecial.S63CD4Inputs

public section

namespace CFSG.Quasithin.Background.Harris.R1.D4Vert

open CFSG.LargeExtraspecial.S63

@[expose] def gensInvolOK (_ : Unit := ()) : Bool :=
  (List.range 8).all fun k => mulR d4Gens[k]! d4Gens[k]! == oneR

@[expose] def substWord {m : ℕ} (W : List (List ℕ)) (r : List (Fin m × Bool)) : List ℕ :=
  r.flatMap fun p => if p.2 then W.getD p.1 [] else (W.getD p.1 []).reverse

@[expose] def relsHold {m : ℕ} (W : List (List ℕ)) (rels : List (List (Fin m × Bool))) : Bool :=
  rels.all fun r => wordR d4Gens (substWord W r) == oneR

end CFSG.Quasithin.Background.Harris.R1.D4Vert
