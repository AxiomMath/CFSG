module

public import CFSG.Quasithin.Recognition.L34AmalgamIsoGLInputs
public import Mathlib

public section

namespace CFSG.KC.L34Mod

open CFSG.Quasithin.L34Amalgam

@[expose] def ord3B (v : Fin 4 → Fin 16) : Bool :=
  (List.finRange 4).all fun i => lin v (lin v (lin v (basisVec i))) == basisVec i

@[expose] def fpfB (v : Fin 4 → Fin 16) : Bool :=
  (List.finRange 16).all fun x => x == 0 || lin v x != x

@[expose] def invB (u : Fin 4 → Fin 16) : Bool :=
  (List.finRange 4).all fun i => lin u (lin u (basisVec i)) == basisVec i

@[expose] def gOf (v : Fin 4 → Fin 16) (b : Fin 16) : Fin 4 → Fin 16 :=
  ![1, v 0, b, bxor (bxor (v 0) b) (lin v b)]

@[expose] def conjB (v : Fin 4 → Fin 16) (b : Fin 16) : Bool :=
  (List.finRange 16).all (fun x => x == 0 || lin (gOf v b) x != 0) &&
    (List.finRange 4).all fun i => lin (gOf v b) (refB i) == lin v (gOf v b i)

@[expose] def s1 (t : Nat) : Bool :=
  !(ord3B (ofCode t) && fpfB (ofCode t)) || (List.finRange 16).any (conjB (ofCode t))

@[expose] def s2 (t : Nat) : Bool :=
  !(invB (ofCode t)) || checkPair (ofCode t) refB

end CFSG.KC.L34Mod
