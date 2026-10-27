module

public import Std.Data.HashSet

public section

namespace Certificates.A6C

abbrev Mat := Array Nat

@[expose] def mulN (n : Nat) (x y : Mat) : Mat :=
  let ks := List.range n
  Array.ofFn (n := n * n) fun p =>
    (ks.foldl (fun s k => s + x[n * (p.val / n) + k]! * y[n * k + p.val % n]!) 0) % 3

@[expose] def trN (n : Nat) (x : Mat) : Mat :=
  Array.ofFn (n := n * n) fun p => x[n * (p.val % n) + p.val / n]!

@[expose] def negM (x : Mat) : Mat := x.map fun e => (2 * e) % 3

@[expose] def idN (n : Nat) : Mat :=
  Array.ofFn (n := n * n) fun p => if p.val / n == p.val % n then 1 else 0

@[expose] def addM (x y : Mat) : Mat :=
  Array.ofFn (n := x.size) fun p => (x[p.val]! + y[p.val]!) % 3

@[expose] def powM (n : Nat) (x : Mat) : Nat → Mat
  | 0 => idN n
  | k + 1 => mulN n x (powM n x k)

@[expose] def conjN (n : Nat) (g x : Mat) : Mat := mulN n (mulN n g x) (trN n g)

@[expose] def packM (x : Mat) : Nat := x.foldl (fun k e => k * 3 + e) 0

@[expose] def keyM (x : Mat) : Nat := min (packM x) (packM (negM x))

@[expose] def eqP (x y : Mat) : Bool := x == y || x == negM y

@[expose] def commP (n : Nat) (x y : Mat) : Bool := eqP (mulN n x y) (mulN n y x)

@[expose] def simOK (n : Nat) (g : Mat) : Bool :=
  g.size == n * n && g.all (· < 3) &&
    (mulN n g (trN n g) == idN n || mulN n g (trN n g) == negM (idN n))

@[expose] def relP (n : Nat) (a x : Mat) : Bool :=
  eqP (mulN n a a) (idN n) && eqP (powM n (mulN n a x) 4) (idN n) &&
    eqP (powM n (mulN n (mulN n x a) x) 5) (idN n)

structure Rec where
  L : Array Mat
  par : Array Nat
  lab : Array Nat

@[expose] def k0Of (n : Nat) (g0 : Mat) (r : Rec) : List Mat :=
  r.L.toList.filter fun c => commP n c g0

@[expose] def conjStep (n : Nat) (G : Array Mat) (j : Nat) (x : Mat) : Mat := conjN n G[j]! x

@[expose] def leftStep (n : Nat) (G : Array Mat) (j : Nat) (x : Mat) : Mat := mulN n G[j]! x

@[expose] def derivOK (step : Nat → Mat → Mat) (k : Nat) (x0 : Mat) (r : Rec) (N : Nat) :
    Bool :=
  r.L.size == N && r.par.size == N && r.lab.size == N && eqP r.L[0]! x0 &&
    (List.range N).all fun i => i == 0 ||
      (r.par[i]! < i && r.lab[i]! < k && eqP r.L[i]! (step r.lab[i]! r.L[r.par[i]!]!))

@[expose] def nodupKeys (ks : List Nat) : Bool :=
  let s := ks.mergeSort (fun a b => decide (a ≤ b))
  (s.zip s.tail).all fun p => decide (p.1 < p.2)

@[expose] def keysNodup (L : Array Mat) : Bool := nodupKeys (L.toList.map keyM)

@[expose] def classOK (n : Nat) (G : Array Mat) (x0 : Mat) (r : Rec) (N : Nat) : Bool :=
  G.all (simOK n) && simOK n x0 && derivOK (conjStep n G) G.size x0 r N && keysNodup r.L

@[expose] def centOK (n : Nat) (E : Array Mat) (x0 : Mat) (r : Rec) (N : Nat) : Bool :=
  E.all (fun e => simOK n e && commP n e x0) &&
    derivOK (leftStep n E) E.size (idN n) r N && keysNodup r.L

@[expose] def reflM (n : Nat) (v : Array Nat) : Mat :=
  let q := (v.foldl (fun s e => s + e * e) 0) % 3
  let inv := if q == 1 then 1 else 2
  Array.ofFn (n := n * n) fun p =>
    let i := p.val / n
    let j := p.val % n
    ((if i == j then 1 else 0) + 9 - 2 * ((v[i]! * inv) % 3) * v[j]!) % 3

end Certificates.A6C
