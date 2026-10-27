module

public import Certificates.Data.CFSGNative.SporLat.Spec

public section

namespace CFSG.Quasithin.H13.KGE64

open CFSG.QuasithinUnique.Ch1.SporLat

@[expose] def tMul (s t : Array Nat) : Array Nat := t.map fun p => s.getD p 0

@[expose] def tId (n : Nat) : Array Nat := (List.range n).toArray

@[expose] def tPow (n : Nat) (y : Array Nat) : Nat → Array Nat
  | 0 => tId n
  | k + 1 => tMul y (tPow n y k)

@[expose] def powers (n : Nat) (y : Array Nat) : Array (Array Nat) :=
  (List.range 8).toArray.map (tPow n y)

@[expose] def ev (ts : List (Array Nat)) (p : Nat) : Nat := ts.foldr (fun t q => t.getD q 0) p

@[expose] def isId (B : List Nat) (ts : List (Array Nat)) : Bool := B.all fun p => ev ts p == p

@[expose] def eqOn (B : List Nat) (us vs : List (Array Nat)) : Bool :=
  B.all fun p => ev us p == ev vs p

@[expose] def cj (pw : Array (Array Nat)) (a : Array Nat) (i : Nat) : List (Array Nat) :=
  [pw.getD i #[], a, pw.getD (7 - i) #[]]

@[expose] def condA (B : List Nat) (pw : Array (Array Nat)) (a : Array Nat) : Bool :=
  !isId B [a] && isId B [a, a] && isId B (cj pw a 3 ++ cj pw a 1 ++ [a])

@[expose] def condB (B : List Nat) (pw : Array (Array Nat)) (b : Array Nat) : Bool :=
  !isId B [b] && isId B [b, b] && isId B (cj pw b 3 ++ cj pw b 2 ++ [b])

@[expose] def commAll (B : List Nat) (pw : Array (Array Nat)) (a b : Array Nat) : Bool :=
  (List.range 3).all fun i => (List.range 3).all fun j =>
    eqOn B (cj pw a i ++ cj pw b j) (cj pw b j ++ cj pw a i)

@[expose] def pairCheck (n : Nat) (B : List Nat) (y : Array Nat) (ts : List (Array Nat)) : Bool :=
  (List.range' 1 6).all fun k =>
    let pw := powers n (tPow n y k)
    let A := ts.filter (condA B pw)
    let Bs := ts.filter (condB B pw)
    A.all fun a => Bs.all fun b => !commAll B pw a b

@[expose] def e64Check {Lab : Type} [DecidableEq Lab] (n : Nat) (B : List Nat)
    (act : Array Nat → Lab → Lab) (ltabs : Array (Array Nat)) (yw : List Nat)
    (ows : List (List Nat)) (labels : List Lab) : Bool :=
  let y := wordTabA ltabs n yw
  let ts := ows.map (wordTabA ltabs n)
  yw.all (· < ltabs.size) && ows.all (fun w => w.all (· < ltabs.size)) &&
    isId B (List.replicate 7 y) && !isId B [y] &&
    decide ((ts.map fun t => B.map fun p => t.getD p 0).Nodup) &&
    ts.all (fun t => labels.all fun L => decide (act t L = L)) && pairCheck n B y ts

end CFSG.Quasithin.H13.KGE64
