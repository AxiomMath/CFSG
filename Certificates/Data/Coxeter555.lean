module

public import CFSG.Certificates.CosetTablePresented
public import Mathlib

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Coxeter555

open CFSG.CosetTable

@[expose] def axWord : List (Fin 3 × Bool) := [(0, true), (1, true)]

@[expose] def rels555 : List (List (Fin 3 × Bool)) :=
  [[(0, true), (0, true)], [(1, true), (1, true)], [(2, true), (2, true)],
    [(1, true), (2, true), (1, true), (2, true)],
    (List.replicate 5 axWord).flatten,
    (List.replicate 5 [(0, true), (2, true)]).flatten,
    (List.replicate 5 [(0, true), (1, true), (2, true)]).flatten]

@[expose] def coxeter555Check : Bool := check (presParams rels555 [axWord]) 2000 132

end CFSG.EvenSporadicStandard.HNRecog.Coxeter555
