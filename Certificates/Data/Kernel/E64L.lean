module

public import Certificates.Data.Kernel.E64F
public import Certificates.Data.CFSGNative.SporLat.Code

public section

namespace CFSG.KC.E64L

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.KC.E64F

@[expose] def tMulT (s t : List Nat) : List Nat := t.map fun p => s.getD p 0

@[expose] def tPowT (n : Nat) (y : List Nat) : Nat → List Nat
  | 0 => List.range n
  | k + 1 => tMulT y (tPowT n y k)

@[expose] def powersT (n : Nat) (y : List Nat) : List (List Nat) := (List.range 8).map (tPowT n y)

@[expose] def evT (ts : List (List Nat)) (p : Nat) : Nat := ts.foldr (fun t q => t.getD q 0) p

@[expose] def isIdT (B : List Nat) (ts : List (List Nat)) : Bool := B.all fun p => evT ts p == p

@[expose] def eqOnT (B : List Nat) (us vs : List (List Nat)) : Bool :=
  B.all fun p => evT us p == evT vs p

@[expose] def cjT (pw : List (List Nat)) (a : List Nat) (i : Nat) : List (List Nat) :=
  [pw.getD i [], a, pw.getD (7 - i) []]

@[expose] def condAT (B : List Nat) (pw : List (List Nat)) (a : List Nat) : Bool :=
  !isIdT B [a] && isIdT B [a, a] && isIdT B (cjT pw a 3 ++ cjT pw a 1 ++ [a])

@[expose] def condBT (B : List Nat) (pw : List (List Nat)) (b : List Nat) : Bool :=
  !isIdT B [b] && isIdT B [b, b] && isIdT B (cjT pw b 3 ++ cjT pw b 2 ++ [b])

@[expose] def commAllT (B : List Nat) (pw : List (List Nat)) (a b : List Nat) : Bool :=
  (List.range 3).all fun i => (List.range 3).all fun j =>
    eqOnT B (cjT pw a i ++ cjT pw b j) (cjT pw b j ++ cjT pw a i)

@[expose] def pairKT (n : Nat) (B : List Nat) (y : List Nat) (ts : List (List Nat)) (k : Nat) :
    Bool :=
  (ts.filter (condAT B (powersT n (tPowT n y k)))).isEmpty ||
    (ts.filter (condBT B (powersT n (tPowT n y k)))).isEmpty ||
    (ts.filter (condAT B (powersT n (tPowT n y k)))).all fun a =>
      (ts.filter (condBT B (powersT n (tPowT n y k)))).all fun b =>
        !commAllT B (powersT n (tPowT n y k)) a b

@[expose] def wordImgT (tabs : List (List Nat)) (w : List Nat) (p : Nat) : Nat :=
  w.foldr (fun l q => (tabs.getD l []).getD q 0) p

@[expose] def wordTabT (tabs : List (List Nat)) (n : Nat) (w : List Nat) : List Nat :=
  (List.range n).map (wordImgT tabs w)

@[expose] def codeATL (n : Nat) (t : List Nat) (c : Nat) : Nat :=
  encodeSet n (insN ((decodeSet n c c).map fun p => t.getD p 0))

@[expose] def codeSetTL (n : Nat) (t : List Nat) (x : List Nat) : List Nat :=
  insN (x.map (codeATL n t))

@[expose] def e64CheckT {Lab : Type} [DecidableEq Lab] (n : Nat) (B : List Nat)
    (act : List Nat → Lab → Lab) (ltabs : List (List Nat)) (yw : List Nat)
    (ows : List (List Nat)) (labels : List Lab) : Bool :=
  yw.all (· < ltabs.length) && ows.all (fun w => w.all (· < ltabs.length)) &&
    isIdT B (List.replicate 7 (wordTabT ltabs n yw)) && !isIdT B [wordTabT ltabs n yw] &&
    decide (((ows.map (wordTabT ltabs n)).map fun t => B.map fun p => t.getD p 0).Nodup) &&
    (ows.map (wordTabT ltabs n)).all (fun t => labels.all fun L => decide (act t L = L)) &&
    (List.range' 1 6).all (pairKT n B (wordTabT ltabs n yw) (ows.map (wordTabT ltabs n)))

end CFSG.KC.E64L

end
