module

public import Mathlib.Logic.Function.Iterate

public section

namespace CFSG.KC.E64F

@[expose] def wordF (L : Nat → Nat → Nat) (w : List Nat) (p : Nat) : Nat :=
  w.foldr (fun l q => L l q) p

@[expose] def evF (fs : List (Nat → Nat)) (p : Nat) : Nat := fs.foldr (fun f q => f q) p

@[expose] def isIdF (B : List Nat) (fs : List (Nat → Nat)) : Bool := B.all fun p => evF fs p == p

@[expose] def eqOnF (B : List Nat) (us vs : List (Nat → Nat)) : Bool :=
  B.all fun p => evF us p == evF vs p

@[expose] def cjF (Y a : Nat → Nat) (i : Nat) : List (Nat → Nat) := [Y^[i], a, Y^[7 - i]]

@[expose] def condAF (B : List Nat) (Y a : Nat → Nat) : Bool :=
  !isIdF B [a] && isIdF B [a, a] && isIdF B (cjF Y a 3 ++ cjF Y a 1 ++ [a])

@[expose] def condBF (B : List Nat) (Y b : Nat → Nat) : Bool :=
  !isIdF B [b] && isIdF B [b, b] && isIdF B (cjF Y b 3 ++ cjF Y b 2 ++ [b])

@[expose] def commAllF (B : List Nat) (Y a b : Nat → Nat) : Bool :=
  (List.range 3).all fun i => (List.range 3).all fun j =>
    eqOnF B (cjF Y a i ++ cjF Y b j) (cjF Y b j ++ cjF Y a i)

@[expose] def pairCheckF (B : List Nat) (y : Nat → Nat) (fs : List (Nat → Nat)) : Bool :=
  (List.range' 1 6).all fun k =>
    (fs.filter (condAF B y^[k])).all fun a =>
      (fs.filter (condBF B y^[k])).all fun b => !commAllF B y^[k] a b

@[expose] def insO (a : Nat) : List Nat → List Nat
  | [] => [a]
  | b :: l => bif Nat.ble a b then a :: b :: l else b :: insO a l

@[expose] def insN : List Nat → List Nat
  | [] => []
  | a :: l => insO a (insN l)

@[expose] def e64CheckF (B : List Nat) (L : Nat → Nat → Nat) (m : Nat) (yw : List Nat)
    (ows : List (List Nat)) (labels : List (List Nat)) : Bool :=
  yw.all (· < m) && ows.all (fun w => w.all (· < m)) &&
    isIdF B (List.replicate 7 (wordF L yw)) && !isIdF B [wordF L yw] &&
    decide ((ows.map fun w => B.map (wordF L w)).Nodup) &&
    ows.all (fun w => labels.all fun Lb =>
      decide (insN (Lb.map (wordF L w)) = Lb)) &&
    pairCheckF B (wordF L yw) (ows.map (wordF L))

end CFSG.KC.E64F

end
