module

public import Init.Data.List.Basic

public section

namespace CFSG.KC.A6C5

@[expose] def en (x : List Nat) (i j : Nat) : Nat := x.getD (5 * i + j) 0

@[expose] def mulL (x y : List Nat) : List Nat :=
  (List.range 25).map fun p =>
    (en x (p / 5) 0 * en y 0 (p % 5) + en x (p / 5) 1 * en y 1 (p % 5) +
      en x (p / 5) 2 * en y 2 (p % 5) + en x (p / 5) 3 * en y 3 (p % 5) +
      en x (p / 5) 4 * en y 4 (p % 5)) % 3

@[expose] def addL (x y : List Nat) : List Nat :=
  (List.range 25).map fun p => (en x (p / 5) (p % 5) + en y (p / 5) (p % 5)) % 3

@[expose] def trL (x : List Nat) : List Nat := (List.range 25).map fun p => en x (p % 5) (p / 5)

@[expose] def negL (x : List Nat) : List Nat :=
  (List.range 25).map fun p => 2 * en x (p / 5) (p % 5) % 3

@[expose] def idL : List Nat := (List.range 25).map fun p => if p / 5 = p % 5 then 1 else 0

@[expose] def powL (x : List Nat) : Nat → List Nat
  | 0 => idL
  | k + 1 => mulL x (powL x k)

@[expose] def eqS (x y : List Nat) : Bool := x == y || x == negL y

@[expose] def simL (x : List Nat) : Bool := eqS (mulL x (trL x)) idL

@[expose] def commL (x y : List Nat) : Bool := eqS (mulL x y) (mulL y x)

@[expose] def cnB (x : List Nat) : Bool := x.length == 25 && x.all fun e => decide (e < 3)

@[expose] def g0L : List Nat :=
  [1,1,2,1,0, 2,0,1,2,1, 1,1,2,0,2, 0,1,2,1,2, 1,1,0,1,2]

@[expose] def nL : List Nat :=
  [0,0,1,0,0, 0,1,0,0,0, 0,0,0,2,0, 0,0,0,0,2, 1,0,0,0,0]

@[expose] def zL : List Nat :=
  [0,2,1,2,1, 2,0,2,1,2, 1,2,0,2,1, 2,1,2,0,2, 1,2,1,2,0]

@[expose] def bInv : List Nat :=
  [1,0,0,2,2, 0,2,2,0,1, 0,0,2,2,1, 0,1,0,2,1, 0,2,0,2,2]

@[expose] def colL (a b c d e : Nat) : List Nat :=
  [a,0,0,0,0, b,0,0,0,0, c,0,0,0,0, d,0,0,0,0, e,0,0,0,0]

@[expose] def eU (j : Nat) : List Nat := (List.range 25).map fun p => if p = j then 1 else 0

@[expose] def kt (W : List Nat) (j : Nat) : List Nat := mulL (mulL (powL g0L j) W) (eU j)

@[expose] def kryl (W : List Nat) : List Nat :=
  addL (kt W 0) (addL (kt W 1) (addL (kt W 2) (addL (kt W 3) (kt W 4))))

@[expose] def el (i j : Nat) : List Nat := mulL (powL g0L i) (powL zL j)

@[expose] def els : List (List Nat) :=
  [el 0 0, el 1 0, el 2 0, el 3 0, el 4 0, el 0 1, el 1 1, el 2 1, el 3 1, el 4 1]

@[expose] def pwB : List (List Nat) → Bool
  | [] => true
  | x :: xs => xs.all (fun y => !eqS x y) && pwB xs

@[expose] def cand (a b c d e : Nat) : List Nat := mulL (kryl (colL a b c d e)) bInv

@[expose] def candOK (a b c d e : Nat) : Bool :=
  !simL (cand a b c d e) || els.any fun y => eqS (cand a b c d e) y

@[expose] def candA (a : Nat) : Bool :=
  [0, 1, 2].all fun b => [0, 1, 2].all fun c => [0, 1, 2].all fun d => [0, 1, 2].all fun e =>
    candOK a b c d e

@[expose] def basic : Bool :=
  cnB g0L && cnB zL && cnB nL && simL g0L && !eqS g0L idL && powL g0L 5 == idL &&
    simL zL && commL zL g0L && eqS (mulL zL zL) idL &&
    mulL (kryl (colL 1 0 0 0 0)) bInv == idL && pwB els && simL nL &&
    eqS (mulL nL g0L) (mulL (mulL g0L g0L) nL)

end CFSG.KC.A6C5
