module

public import CFSG.Sporadic.Presentation.Co2CoverInputs

public section

namespace CFSG.Sporadic.Presentation.Co2

open CFSG.CosetTable CFSG.Certificates CFSG.Certificates.CosetEnumeration

abbrev ltr (w : List (Fin gc × Bool)) : List (ℕ × Bool) := w.map fun l => ((l.1 : ℕ), l.2)

abbrev gW : List (Fin gc × Bool) := [(gb, true), (gb, true)]

abbrev conjW (i : Fin 4) : List (Fin gc × Bool) :=
  FreeGroup.invRev gW ++ substWord hs (dW.getD i []) ++ gW ++
    FreeGroup.invRev (substWord hs (dpW.getD i []))

abbrev jWords : List (List (ℕ × Bool)) :=
  (R.map (substWord hs)).map ltr ++ (List.finRange 4).map (fun i => ltr (conjW i)) ++
    [ltr (substWord hs w1), ltr (substWord hs w2)]

end CFSG.Sporadic.Presentation.Co2
