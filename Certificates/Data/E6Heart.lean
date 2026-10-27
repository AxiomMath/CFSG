module

public section

namespace Certificates.E6Heart

set_option compiler.extract_closed false

@[expose] def cartan : List (List Int) :=
  [[2, 0, -1, 0, 0, 0], [0, 2, 0, -1, 0, 0], [-1, 0, 2, -1, 0, 0],
   [0, -1, -1, 2, -1, 0], [0, 0, 0, -1, 2, -1], [0, 0, 0, 0, -1, 2]]

@[expose] def roots : List (List Int) :=
  [[1, 0, 0, 0, 0, 0],
   [0, 1, 0, 0, 0, 0],
   [0, 0, 1, 0, 0, 0],
   [0, 0, 0, 1, 0, 0],
   [0, 0, 0, 0, 1, 0],
   [0, 0, 0, 0, 0, 1],
   [-1, 0, 0, 0, 0, 0],
   [1, 0, 1, 0, 0, 0],
   [0, -1, 0, 0, 0, 0],
   [0, 1, 0, 1, 0, 0],
   [0, 0, -1, 0, 0, 0],
   [0, 0, 1, 1, 0, 0],
   [0, 0, 0, -1, 0, 0],
   [0, 0, 0, 1, 1, 0],
   [0, 0, 0, 0, -1, 0],
   [0, 0, 0, 0, 1, 1],
   [0, 0, 0, 0, 0, -1],
   [-1, 0, -1, 0, 0, 0],
   [1, 0, 1, 1, 0, 0],
   [0, -1, 0, -1, 0, 0],
   [0, 1, 1, 1, 0, 0],
   [0, 1, 0, 1, 1, 0],
   [0, 0, -1, -1, 0, 0],
   [0, 0, 1, 1, 1, 0],
   [0, 0, 0, -1, -1, 0],
   [0, 0, 0, 1, 1, 1],
   [0, 0, 0, 0, -1, -1],
   [-1, 0, -1, -1, 0, 0],
   [1, 1, 1, 1, 0, 0],
   [1, 0, 1, 1, 1, 0],
   [0, -1, -1, -1, 0, 0],
   [0, -1, 0, -1, -1, 0],
   [0, 1, 1, 1, 1, 0],
   [0, 1, 0, 1, 1, 1],
   [0, 0, -1, -1, -1, 0],
   [0, 0, 1, 1, 1, 1],
   [0, 0, 0, -1, -1, -1],
   [-1, -1, -1, -1, 0, 0],
   [-1, 0, -1, -1, -1, 0],
   [1, 1, 1, 1, 1, 0],
   [1, 0, 1, 1, 1, 1],
   [0, -1, -1, -1, -1, 0],
   [0, -1, 0, -1, -1, -1],
   [0, 1, 1, 2, 1, 0],
   [0, 1, 1, 1, 1, 1],
   [0, 0, -1, -1, -1, -1],
   [-1, -1, -1, -1, -1, 0],
   [-1, 0, -1, -1, -1, -1],
   [1, 1, 1, 2, 1, 0],
   [1, 1, 1, 1, 1, 1],
   [0, -1, -1, -2, -1, 0],
   [0, -1, -1, -1, -1, -1],
   [0, 1, 1, 2, 1, 1],
   [-1, -1, -1, -2, -1, 0],
   [-1, -1, -1, -1, -1, -1],
   [1, 1, 2, 2, 1, 0],
   [1, 1, 1, 2, 1, 1],
   [0, -1, -1, -2, -1, -1],
   [0, 1, 1, 2, 2, 1],
   [-1, -1, -2, -2, -1, 0],
   [-1, -1, -1, -2, -1, -1],
   [1, 1, 2, 2, 1, 1],
   [1, 1, 1, 2, 2, 1],
   [0, -1, -1, -2, -2, -1],
   [-1, -1, -2, -2, -1, -1],
   [-1, -1, -1, -2, -2, -1],
   [1, 1, 2, 2, 2, 1],
   [-1, -1, -2, -2, -2, -1],
   [1, 1, 2, 3, 2, 1],
   [-1, -1, -2, -3, -2, -1],
   [1, 2, 2, 3, 2, 1],
   [-1, -2, -2, -3, -2, -1]]

@[expose] def cEntry (i j : Nat) : Int := (cartan.getD i []).getD j 0

@[expose] def idx6 : List Nat := [0, 1, 2, 3, 4, 5]

@[expose] def pairZ (a b : List Int) : Int :=
  idx6.foldl (fun s i => s + idx6.foldl (fun t j => t + a.getD i 0 * cEntry i j * b.getD j 0) 0) 0

@[expose] def m3 (z : Int) : Nat := (z % 3).toNat

@[expose] def pair3 (a : List Int) (y : List Nat) : Nat :=
  m3 (pairZ a (y.map (fun (u : Nat) => (u : Int))))

@[expose] def qOf (y : List Nat) : Nat :=
  m3 (pairZ (y.map (fun (u : Nat) => (u : Int))) (y.map (fun (u : Nat) => (u : Int))))

@[expose] def rootAt (i : Nat) : List Int := roots.getD i []

@[expose] def repL (t : Nat) : List Nat :=
  [0, t % 3, t / 3 % 3, t / 9 % 3, t / 27 % 3, t / 81 % 3]

@[expose] def phiL (y : List Nat) : List Nat :=
  (List.range 72).filter (fun i => pair3 (rootAt i) y == 0)

@[expose] def adjB (i j : Nat) : Bool := i != j && pairZ (rootAt i) (rootAt j) != 0

@[expose] def stepL (pm seen : List Nat) : List Nat :=
  seen ++ pm.filter (fun j => !seen.contains j && seen.any (fun i => adjB i j))

@[expose] def iterStep (pm : List Nat) : Nat → List Nat → List Nat
  | 0, seen => seen
  | k + 1, seen =>
    let next := stepL pm seen
    if next.length == seen.length then seen else iterStep pm k next

@[expose] def compOf (pm : List Nat) (seed : Nat) : List Nat := iterStep pm 72 [seed]

@[expose] def closedIn (pm c : List Nat) : Bool :=
  pm.all (fun j => c.contains j || !c.any (fun i => adjB i j))

@[expose] def kerSize (c : List Nat) : Nat :=
  ((List.range 243).filter (fun t => c.all (fun i => pair3 (rootAt i) (repL t) == 0))).length

@[expose] def goodAt (t : Nat) : Bool :=
  let y := repL t
  let pm := phiL y
  let q := qOf y
  let ps := pm.map (fun i => (i, compOf pm i))
  ps.all (fun p => closedIn pm p.2) &&
    (if q == 0 then ps.all (fun p => p.2.length ≤ 6)
     else
      ps.all (fun p => p.2.length ≤ 6 ||
          ps.all (fun r => r.2.length ≤ 6 || p.2.contains r.1)) &&
        ps.any (fun p => p.2.length == (if q == 1 then 24 else 30) && kerSize p.2 == 3))

@[expose] def reflV (i : Nat) (a : List Int) : List Int :=
  idx6.map (fun k => a.getD k 0 -
    (if k == i then pairZ a (idx6.map (fun j => if j == i then 1 else 0)) else 0))

@[expose] def unitV (i : Nat) : List Int := idx6.map (fun j => if j == i then 1 else 0)

@[expose] def rootsOk (_ : Unit := ()) : Bool :=
  roots.length == 72 && roots.all (fun a => a.length == 6 && pairZ a a == 2) &&
    (List.range 72).all (fun i => (List.range i).all (fun j => rootAt i != rootAt j)) &&
    roots.take 6 == idx6.map unitV &&
    (List.range 72).all (fun i => i < 6 ||
      (List.range i).any (fun j => idx6.any (fun k => reflV k (rootAt j) == rootAt i))) &&
    roots.all (fun a => idx6.all (fun i => roots.contains (reflV i a)))

@[expose] def radOk (_ : Unit := ()) : Bool :=
  ((List.range 729).filter (fun v =>
      idx6.all (fun i => m3 (idx6.foldl (fun s j =>
        s + cEntry i j * ((v / 3 ^ j % 3 : Nat) : Int)) 0) == 0))) == [0, 416, 586]

@[expose] def cntQ (q : Nat) : Nat :=
  ((List.range 243).filter (fun t => t != 0 && qOf (repL t) == q)).length

@[expose] def check (_ : Unit := ()) : Bool :=
  rootsOk () && radOk () && (List.range 243).all (fun t => t == 0 || goodAt t) &&
    cntQ 0 == 80 && cntQ 1 == 90 && cntQ 2 == 72

end Certificates.E6Heart
