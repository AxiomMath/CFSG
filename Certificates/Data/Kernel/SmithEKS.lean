module

public import Certificates.Data.Kernel.SmithEKF
public import Certificates.Data.SmithECheck

public section

namespace CFSG.SmithE.K

open CFSG.F4.Native CFSG.SmithE

@[expose] def m01 : Nat := (4 ^ 37 - 1) / 3

@[expose] def wM (Q : Nat) : Nat :=
  let L := Q &&& m01
  let H := (Q >>> 1) &&& m01
  H ||| ((L ^^^ H) <<< 1)

@[expose] def wM2 (Q : Nat) : Nat :=
  let L := Q &&& m01
  let H := (Q >>> 1) &&& m01
  (L ^^^ H) ||| (L <<< 1)

@[expose] def tvW (T : List (List (List (List Nat)))) (p : Nat) : List Nat :=
  let Q := qOf p
  hQ T Q (wM Q) (wM2 Q)

@[expose] def applyL : List Nat → Nat → Nat
  | [], _ => 0
  | x :: l, c => (if c.testBit 0 then x else 0) ^^^ applyL l (c / 2)

@[expose] def gensL (L : List Nat) : List Nat := L.zipIdx.map fun xm => xm.1 ^^^ 2 ^ xm.2

@[expose] def coefOf (E : List (Nat × Nat)) (v : Nat) : Nat :=
  (List.range E.length).foldl (fun acc i => if v.testBit (E[i]!).1 then acc + 2 ^ i else acc) 0

@[expose] def coefR : List (Nat × Nat) → Nat → Nat
  | [], _ => 0
  | be :: E, v => (if v.testBit be.1 then 1 else 0) + 2 * coefR E v

@[expose] def spanOKL (L : List Nat) : Bool :=
  let G := gensL L
  let E := G.foldl insertVec []
  let B := E.map (·.2)
  let S := (List.range 20).map fun m => reduceBy E (2 ^ m)
  E.length == 6 && (B.all fun b => applyL S b == 0) && G.all fun v => let c := coefR E v
    decide (c < 64) && applyL B c == v

end CFSG.SmithE.K
