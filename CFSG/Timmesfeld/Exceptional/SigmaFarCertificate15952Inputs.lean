module

public import CFSG.Timmesfeld.Exceptional.TwoLines

public section

namespace CFSG.Timmesfeld.Moufang

open CFSG.Certificates CFSG.Certificates.CosetEnumeration

namespace SigmaFar

open TwoLines

@[expose] def wXD : List (Fin 3 × Bool) := [(1, true)] ++ wD

@[expose] def relsF4 : List (List (Fin 3 × Bool)) := relsD ++ [(List.replicate 4 wXD).flatten]

@[expose] def relsF3 : List (List (Fin 3 × Bool)) := relsD ++ [(List.replicate 3 wXD).flatten]

@[expose] def wU : List (Fin 3 × Bool) := (List.replicate 12 ([(2, true)] ++ wD)).flatten

@[expose] def subK : List (List (Fin 3 × Bool)) := [[(0, true)], [(1, true)], wD]

@[expose] def relsK : List (List (Fin 3 × Bool)) :=
  [[(0, true), (0, true)], [(1, true), (1, true)], [(2, true), (2, true)],
    (List.replicate 4 [(0, true), (1, true)]).flatten,
    (List.replicate 2 [(0, true), (2, true)]).flatten,
    (List.replicate 2 [(0, true), (1, true), (0, true), (1, true), (2, true)]).flatten ++
      [(0, true)],
    (List.replicate 3 [(1, true), (2, true)]).flatten]

@[expose] def σ : Fin 3 → Equiv.Perm (Fin 7) :=
  ![Equiv.swap 0 2 * Equiv.swap 3 5, Equiv.swap 3 4 * Equiv.swap 5 6,
    Equiv.swap 0 6 * Equiv.swap 1 3]

@[expose] def τ : Fin 3 → Equiv.Perm (Fin 7) := ![σ 0, σ 1, signedProd σ wD]

@[expose] def w24 : Fin 24 → List (Fin 3 × Bool) :=
  ![[], [(0, true)], [(1, true)], [(2, true)], [(0, true), (1, true)], [(0, true), (2, true)],
    [(1, true), (0, true)], [(1, true), (2, true)], [(2, true), (1, true)],
    [(0, true), (1, true), (0, true)], [(0, true), (1, true), (2, true)],
    [(0, true), (2, true), (1, true)], [(1, true), (0, true), (1, true)],
    [(1, true), (0, true), (2, true)], [(1, true), (2, true), (1, true)],
    [(2, true), (1, true), (0, true)], [(0, true), (1, true), (0, true), (1, true)],
    [(0, true), (1, true), (0, true), (2, true)], [(0, true), (1, true), (2, true), (1, true)],
    [(0, true), (2, true), (1, true), (0, true)], [(1, true), (0, true), (1, true), (2, true)],
    [(1, true), (0, true), (2, true), (1, true)], [(1, true), (2, true), (1, true), (0, true)],
    [(2, true), (1, true), (0, true), (1, true)]]

end SigmaFar

end CFSG.Timmesfeld.Moufang
