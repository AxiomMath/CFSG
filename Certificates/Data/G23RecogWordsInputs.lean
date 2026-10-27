module

public import CFSG.Certificates.CosetTablePresented
public import Mathlib

public section

namespace CFSG.GH74.QTGen4.Recog.G23

open CFSG.CosetTable

@[expose] def g23WordsH : List (List (Fin 6 × Bool)) := [
  [(0, true), (0, true), (0, true)],
  [(1, true), (1, true), (1, true)],
  [(1, false), (0, false), (1, true), (0, false), (1, false), (0, true)],
  [(2, true), (2, true), (2, true)],
  [(3, true), (3, true), (3, true)],
  [(3, false), (2, false), (3, true), (2, false), (3, false), (2, true)],
  [(0, true), (1, true), (0, true), (1, true), (3, false), (2, false), (3, false), (2, false)],
  [(0, false), (2, false), (0, true), (2, true)],
  [(0, false), (3, false), (0, true), (3, true)],
  [(1, false), (2, false), (1, true), (2, true)],
  [(1, false), (3, false), (1, true), (3, true)],
  [(4, true), (4, true)],
  [(4, true), (0, true), (4, true), (0, true)],
  [(4, true), (1, true), (4, true), (1, true)],
  [(4, true), (2, true), (4, true), (2, true)],
  [(4, true), (3, true), (4, true), (3, true)]
]

@[expose] def evalW {X : Type*} [Group X] (e : Fin 6 → X) (r : List (Fin 6 × Bool)) : X :=
  FreeGroup.lift e (FreeGroup.mk r)

@[expose] def dWord₁ : List (Fin 6 × Bool) := [(1, false), (2, false)]

@[expose] def dWord₂ : List (Fin 6 × Bool) := [(4, true), (1, true), (3, true), (0, false)]

@[expose] def invWord (w : List (Fin 6 × Bool)) : List (Fin 6 × Bool) :=
  (w.map fun l => (l.1, !l.2)).reverse

@[expose] def substWord (r : List (Fin 3 × Bool)) : List (Fin 6 × Bool) :=
  r.flatMap fun l =>
    if l.1 = 0 then (if l.2 then dWord₁ else invWord dWord₁)
    else if l.1 = 1 then (if l.2 then dWord₂ else invWord dWord₂)
    else [(5, l.2)]

@[expose] def g23PM : List (List (Fin 3 × Bool)) := [
  [(0, true), (0, true), (0, true)],
  [(2, true), (0, false), (2, true), (0, true), (2, false), (2, false), (0, true)],
  [(1, false), (2, false), (1, true), (1, true), (0, false), (2, false), (0, true)],
  [(1, true), (1, true), (2, false), (1, false), (1, false), (2, true), (0, false), (1, true)],
  [(2, true), (0, true), (2, true), (1, false), (2, true), (0, true), (2, true), (1, false)],
  [(1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true)],
  [(1, false), (0, true), (1, true), (1, true), (0, false), (1, true), (0, false), (1, false), (1, false), (0, true)],
  [(1, true), (0, false), (2, true), (1, true), (2, false), (2, false), (1, true), (0, true), (1, true), (0, false)]
]

@[expose] def g23PD : List (List (Fin 2 × Bool)) := [
  [(0, true), (0, true), (0, true)],
  [(1, true), (0, false), (1, false), (0, false), (1, true), (0, false), (1, false), (0, false)],
  [(1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true)],
  [(1, true), (0, true), (1, false), (0, false), (1, true), (1, true), (0, true), (1, false), (0, false), (1, true)]
]

@[expose] def g23WordsM : List (List (Fin 6 × Bool)) :=
  g23PM.map fun r => FreeGroup.reduce (substWord r)

@[expose] def g23WordsCycle : List (List (Fin 6 × Bool)) := [
  [(3, true), (5, true), (3, true), (5, true), (3, true), (5, true), (3, true), (5, true), (3, true), (5, true), (3, true), (5, true)],
  [(1, true), (0, false), (5, true), (1, true), (0, false), (5, true), (1, true), (0, false), (5, true), (1, true), (0, false), (5, true), (1, true), (0, false), (5, true), (1, true), (0, false), (5, true)]
]

@[expose] def g23Words : List (List (Fin 6 × Bool)) := g23WordsH ++ g23WordsM ++ g23WordsCycle

end CFSG.GH74.QTGen4.Recog.G23
