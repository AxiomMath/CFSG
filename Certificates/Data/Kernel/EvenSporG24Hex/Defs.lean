module

public section

namespace CFSG.KC.EvenSporG24Hex

@[expose] def dig (x i : Nat) : Nat := x / 4 ^ i % 4

@[expose] def mulN (s c : Nat) : Nat :=
  (s % 2 * (c % 2) + s / 2 % 2 * (c / 2 % 2)) % 2 +
    2 * ((s % 2 * (c / 2 % 2) + s / 2 % 2 * (c % 2) + s / 2 % 2 * (c / 2 % 2)) % 2)

@[expose] def hor : (Nat → Nat) → Nat → Nat
  | _, 0 => 0
  | g, n + 1 => g 0 + 4 * hor (fun i => g (i + 1)) n

@[expose] def scaleD (s x : Nat) : Nat := hor (fun i => mulN s (dig x i)) 14

@[expose] def codesK (u w : Nat) : List Nat :=
  (List.range 4).flatMap fun c => (List.range 4).filterMap fun d =>
    if c = 0 ∧ d = 0 then none else some (scaleD c u ^^^ scaleD d w)

@[expose] def insN (a : Nat) : List Nat → List Nat
  | [] => [a]
  | b :: l => if a ≤ b then a :: b :: l else b :: insN a l

@[expose] def isortN : List Nat → List Nat
  | [] => []
  | b :: l => insN b (isortN l)

@[expose] def strictInc : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: l => decide (a < b) && strictInc (b :: l)

@[expose] def pk (w : Nat) : List Nat → Nat
  | [] => 0
  | x :: l => x + 2 ^ w * pk w l

@[expose] def fld (w P k : Nat) : Nat := (P >>> (w * k)) % 2 ^ w

@[expose] def memP (x B : Nat) : Bool := (List.range 15).any fun q => fld 28 B q == x

@[expose] def csOf (E : List Nat) : List Nat :=
  (List.range 56).map fun q => hor (fun a => mulN (E.getD (14 * a + q / 4) 0 % 4) (q % 4)) 14

@[expose] def xorN (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => xorN f n ^^^ f n

@[expose] def mulP (C x : Nat) : Nat := xorN (fun b => fld 28 C (4 * b + dig x b)) 14

@[expose] def ilv : List Nat → List Nat → List Nat
  | u :: us, w :: ws => u :: w :: ilv us ws
  | _, _ => []

@[expose] def eqL : List Nat → List Nat → Bool
  | [], [] => true
  | a :: l, b :: m => Nat.beq a b && eqL l m
  | _, _ => false

@[expose] def dataOK (T U W : List Nat) (GE PG : List (List Nat)) : Bool :=
  U.length == 1365 && W.length == 1365 && eqL (T.take 2730) (ilv U W) && GE.length == 16 &&
    GE.all (·.length == 196) && eqL ((T.drop 2730).take 3136) GE.flatten && PG.length == 16 &&
    PG.all (·.length == 1365) && eqL ((T.drop 5866).take 21840) PG.flatten

@[expose] def linesOK (U W : List Nat) : Bool :=
  (List.range 1365).all fun k =>
    let S := isortN (codesK (U.getD k 0) (W.getD k 0))
    strictInc S && S.all (· != 0)

@[expose] def keyN (U W : List Nat) (k : Nat) : Nat := pk 28 (isortN (codesK (U.getD k 0) (W.getD k 0)))

@[expose] def keysOK (U W : List Nat) : Bool :=
  strictInc (isortN ((List.range 1365).map (keyN U W)))

@[expose] def lcOK (U W : List Nat) (LC : Nat) : Bool :=
  LC == pk 420 ((List.range 1365).map fun k => pk 28 (codesK (U.getD k 0) (W.getD k 0)))

@[expose] def hexJ (U W : List Nat) (GE PG : List (List Nat)) (LC j : Nat) : Bool :=
  let C := pk 28 (csOf (GE.getD j []))
  let P := PG.getD j []
  (List.range 1365).all fun k =>
    let B := fld 420 LC (P.getD k 0 % 1365)
    memP (mulP C (U.getD k 0)) B && memP (mulP C (W.getD k 0)) B

end CFSG.KC.EvenSporG24Hex
