module

public import CFSG.Certificates.WordSubgroup

public section

namespace CFSG.Sporadic.Recognition.J3Multiplier

open CFSG.CosetTable

@[expose] def rep (n : ℕ) (w : List (Fin 2 × Bool)) : List (Fin 2 × Bool) :=
  (List.replicate n w).flatten

@[expose] def sc : List (Fin 2 × Bool) := [(1, true)]

@[expose] def sm : List (Fin 2 × Bool) := [(0, true), (1, false), (0, false)]

@[expose] def a2 : List (Fin 2 × Bool) := [(0, true), (0, true)]

@[expose] def a2inv : List (Fin 2 × Bool) := [(0, false), (0, false)]

@[expose] def ac3 : List (Fin 2 × Bool) := rep 3 [(0, true), (1, true)]

@[expose] def c19 : List (Fin 2 × Bool) := rep 19 sc

@[expose] def u5 : List (Fin 2 × Bool) := rep 6 sc ++ rep 5 sm

@[expose] def u6 : List (Fin 2 × Bool) :=
  rep 2 (sc ++ sc ++ sm) ++ sc ++ sm ++ sm ++ sc ++ sm

@[expose] def w8 : List (Fin 2 × Bool) := rep 3 sc ++ rep 2 (sc ++ sm)

@[expose] def u8 : List (Fin 2 × Bool) := w8 ++ w8

@[expose] def r5 : List (Fin 2 × Bool) := rep 2 u5

@[expose] def r6 : List (Fin 2 × Bool) := rep 2 u6

@[expose] def r7 : List (Fin 2 × Bool) :=
  sc ++ sc ++ rep 3 (sc ++ sm) ++ sc ++ sc ++ rep 4 (sc ++ sm) ++ sm ++ rep 3 (sc ++ sm)

@[expose] def r8 : List (Fin 2 × Bool) := rep 2 u8

@[expose] def letterOfInt (z : ℤ) : Fin 2 × Bool :=
  (if z.natAbs = 1 then 0 else 1, decide (0 < z))

@[expose] def intWord (l : List ℤ) : List (Fin 2 × Bool) := l.map letterOfInt

@[expose] def genWords : List (List (Fin 2 × Bool)) := [[(0, true)], [(0, true), (1, true)]]

@[expose] def abWords : List (List (Fin 2 × Bool)) := [[(0, true)], [(0, false), (1, true)]]

@[expose] def c5 : List (Fin 2 × Bool) :=
  substWord abWords (intWord [1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2])

@[expose] def c6 : List (Fin 2 × Bool) :=
  substWord abWords (intWord [1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2])

@[expose] def c8 : List (Fin 2 × Bool) :=
  substWord abWords (intWord [-2, 1, -2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, -2,
    1, -2, 1, -2, 1, 2])

@[expose] def conjWord (c u : List (Fin 2 × Bool)) : List (Fin 2 × Bool) :=
  c ++ [(0, true)] ++ FreeGroup.invRev c ++ FreeGroup.invRev u

@[expose] def U : List (List (Fin 2 × Bool)) :=
  [ac3, c19, r5 ++ a2inv, r6 ++ a2inv, r8 ++ a2inv]

@[expose] def T : Fin 2 → List (Fin 2 × Bool) := ![a2, r7]

@[expose] def checkWords : List (List (Fin 2 × Bool)) :=
  U ++ [a2, r7, conjWord c5 u5, conjWord c6 u6, conjWord c8 u8]

@[expose] def natWords : List (List (ℕ × Bool)) :=
  (checkWords.map (substWord genWords)).map fun w => w.map fun l => (l.1.val, l.2)

end CFSG.Sporadic.Recognition.J3Multiplier
