module

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KData

@[expose] def tid (d : Nat) : Array Nat := Array.range d

@[expose] def tcomp (p q : Array Nat) : Array Nat := q.map fun y => p.getD y y

@[expose] def tword (d : Nat) (t₀ t₁ : Array Nat) (w : List Nat) : Array Nat :=
  w.foldr (fun i acc => tcomp (if i = 0 then t₀ else t₁) acc) (tid d)

@[expose] def sW (k : Nat) : List Nat := (List.replicate k [0, 1]).flatten

@[expose] def validT (d : Nat) (t : Array Nat) : Bool :=
  t.size == d && (List.range d).all (fun x => decide (t.getD x x < d)) &&
    (List.range d).all fun x => (List.range x).all fun y => t.getD x x != t.getD y y

@[expose] def tleFrom (a b : Array Nat) (i : Nat) : Bool :=
  if h : i < a.size then
    if a[i] < b.getD i 0 then true
    else if a[i] == b.getD i 0 then tleFrom a b (i + 1) else false
  else true
termination_by a.size - i

@[expose] def tle (a b : Array Nat) : Bool := tleFrom a b 0

@[expose] def mergeAdj : List (Array Nat × Int) → List (Array Nat × Int)
  | [] => []
  | x :: l =>
    match mergeAdj l with
    | y :: r => if x.1 == y.1 then (x.1, x.2 + y.2) :: r else x :: y :: r
    | [] => [x]

@[expose] def nfMod (p : Nat) (l : List (Array Nat × Int)) : List (Array Nat × Int) :=
  ((mergeAdj (l.mergeSort fun x y => tle x.1 y.1)).map fun x => (x.1, x.2 % (p : Int))).filter
    fun x => x.2 != 0

@[expose] def zeroMod (p : Nat) (l : List (Array Nat × Int)) : Bool := (nfMod p l).isEmpty

@[expose] def convNF (p : Nat) (α β : List (Array Nat × Int)) : List (Array Nat × Int) :=
  α.foldl (fun acc a => nfMod p (acc ++ β.map fun b => (tcomp a.1 b.1, a.2 * b.2))) []

@[expose] def letterOf (c : Char) : Nat := if c = 'a' then 0 else 1

@[expose] def parseWord (s : String) : List Nat := s.toList.map letterOf

@[expose] def parsePairs (s : String) : List (List Nat × List Nat) :=
  ((s.splitOn " ").filter fun t => t != "").map fun t =>
    match t.splitOn "." with
    | [x, y] => (parseWord x, parseWord y)
    | _ => ([], [])

@[expose] def parseTerms (s : String) : List (List Nat × Int) :=
  ((s.splitOn " ").filter fun t => t != "").map fun t =>
    match t.splitOn ":" with
    | [c, w] => (parseWord w, c.toInt?.getD 0)
    | _ => ([], 0)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KData
