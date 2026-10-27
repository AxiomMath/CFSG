module

public import CFSG.Sporadic.J4.QTRankNative

public section

namespace CFSG.Sporadic.J4.QT

@[expose] def hWord : List Int := [2, -1, -3, -3, -3, -2, -2, -2, 3, -1, 2, -1, -2]

@[expose] def hT : List Nat := wordT hWord

@[expose] def powT (t : List Nat) : Nat → List Nat
  | 0 => idT
  | n + 1 => compT t (powT t n)

@[expose] def t0 : List Nat := letterTab 1

@[expose] def tp (n : Nat) : List Nat := powT t0 n

@[expose] def tpL : List (List Nat) := (List.range 23).map tp

@[expose] def kvec (i : Nat) : Nat := actT (tp i) 1

@[expose] def kcomb (μ : Nat) : Nat := rowsXor kvec 11 μ

@[expose] def kinv : Array Nat :=
  (List.range 2048).foldl (fun a μ => a.set! (kcomb μ) μ) (Array.replicate 2048 0)

@[expose] def candTab (s w : Nat) : List Nat :=
  let v := (List.range 11).map fun i => actT (tpL.getD ((s * i) % 23) []) w
  (List.range 11).map fun j => rowsXor (fun i => v.getD i 0) 11 (kinv.getD (2 ^ j) 0)

@[expose] def o1 : List Nat := ((orbits.getD 0 (0, [], [])).2.1).map Prod.fst

@[expose] def o2 : List Nat := ((orbits.getD 1 (0, [], [])).2.1).map Prod.fst

@[expose] def fTabs : List (List Nat) :=
  (List.range 23).flatMap fun i => (List.range 11).map fun j => compT (tp i) (powT hT j)

@[expose] def survOK (s w : Nat) : Bool := o1.all fun c => o1.contains (actT (candTab s w) c)

@[expose] def survIn (s w : Nat) : Bool := fTabs.contains (candTab s w)

end CFSG.Sporadic.J4.QT
