module

public section

namespace CFSG.KC.FzUT

@[expose] def f4mulP (a b : Nat) : Nat :=
  (((a &&& b) ^^^ ((a >>> 1) &&& (b >>> 1))) &&& 1) +
    2 * ((((a &&& (b >>> 1)) ^^^ ((a >>> 1) &&& b)) ^^^ ((a >>> 1) &&& (b >>> 1))) &&& 1)

@[expose] def pmulP (i j : Nat) : Nat := i ^^^ j ^^^ 16 * f4mulP (i &&& 3) ((j >>> 2) &&& 3)

@[expose] def pwP (e g : Nat) : Nat := e * g

@[expose] def commP (g h : Nat) : Nat :=
  16 * (f4mulP (g &&& 3) ((h >>> 2) &&& 3) ^^^ f4mulP (h &&& 3) ((g >>> 2) &&& 3))

@[expose] def evN (g1 g2 g3 g4 x : Nat) : Nat :=
  let c' := (x >>> 4) ^^^ f4mulP (x &&& 3) ((x >>> 2) &&& 3)
  pmulP (pmulP (pmulP (pmulP (pmulP (pwP (x &&& 1) g1) (pwP ((x >>> 1) &&& 1) g2))
    (pwP ((x >>> 2) &&& 1) g3)) (pwP ((x >>> 3) &&& 1) g4)) (pwP (c' &&& 1) (commP g1 g3)))
    (pwP ((c' >>> 1) &&& 1) (commP g1 g4))

end CFSG.KC.FzUT
