module

public import Certificates.Data.CFSGNative.SporadicSchreier.Count
public import Std.Data.HashSet

public section

namespace CFSG.Sporadic.Schreier.Native

open CFSG.Sporadic.Th.Native

@[expose] def key (n : Nat) (T : Table) : Nat :=
  (List.range n).foldr (fun i acc => ap T i + n * acc) 0

@[expose] def conjT (n : Nat) (g gi x : Table) : Table := compT n (compT n g x) gi

@[expose] def tblEq (n : Nat) (S T : Table) : Bool := allIn 0 n fun i => ap S i == ap T i

@[expose] def conjClosure (n : Nat) (gens gensInv : Array Table) (x : Table) (cap : Nat) :
    Array Table × Array Nat × Array Nat := Id.run do
  let mut seen : Std.HashSet Nat := (∅ : Std.HashSet Nat).insert (key n x)
  let mut elts : Array Table := #[x]
  let mut par : Array Nat := #[0]
  let mut lab : Array Nat := #[0]
  for h in [0:cap] do
    if h < elts.size then
      let y := elts[h]!
      for l in [0:gens.size] do
        let z := conjT n gens[l]! gensInv[l]! y
        let kz := key n z
        if !seen.contains kz then
          seen := seen.insert kz
          elts := elts.push z
          par := par.push h
          lab := lab.push l
    else break
  return (elts, par, lab)

@[expose] def conjTreeOK (n : Nat) (gens gensInv : Array Table) (x : Table) (elts : Array Table)
    (par lab : Array Nat) : Bool :=
  0 < elts.size && tblEq n elts[0]! x &&
    allIn 1 elts.size fun k => par[k]! < k && lab[k]! < gens.size &&
      tblEq n elts[k]! (conjT n gens[lab[k]!]! gensInv[lab[k]!]! elts[par[k]!]!)

@[expose] def strictlyIncreasing : List Nat → Bool
  | a :: b :: l => a < b && strictlyIncreasing (b :: l)
  | _ => true

@[expose] def keysDistinct (n : Nat) (Ts : List Table) : Bool :=
  strictlyIncreasing ((Ts.map (key n)).mergeSort)

@[expose] def findReps (n : Nat) (gens gensInv : Array Table) (X : List Table) (cap : Nat) :
    List Nat := Id.run do
  let Xa := X.toArray
  let mut seen : Std.HashSet Nat := ∅
  let mut reps : Array Nat := #[]
  for i in [0:Xa.size] do
    let x := Xa[i]!
    if !seen.contains (key n x) then
      reps := reps.push i
      let (elts, _, _) := conjClosure n gens gensInv x cap
      for e in elts do
        seen := seen.insert (key n e)
  return reps.toList

@[expose] def classes (n : Nat) (gens gensInv : Array Table) (X : List Table) (cap : Nat) :
    List (Table × Array Table × Array Nat × Array Nat) :=
  (findReps n gens gensInv X cap).map fun i =>
    (X.toArray[i]!, conjClosure n gens gensInv X.toArray[i]! cap)

@[expose] def classOK (n : Nat) (gens gensInv : Array Table) (X : List Table) (cap : Nat) : Bool :=
  let cl := classes n gens gensInv X cap
  (findReps n gens gensInv X cap).all (· < X.length) &&
    cl.all (fun c => conjTreeOK n gens gensInv c.1 c.2.1 c.2.2.1 c.2.2.2) &&
    keysDistinct n (cl.flatMap fun c => c.2.1.toList) &&
    (cl.map fun c => c.2.1.size).sum == X.length

@[expose] def classTotal (n : Nat) (gens gensInv : Array Table) (X Y : List Table)
    (cap r s mx my : Nat) : Nat :=
  ((classes n gens gensInv X cap).map fun c =>
    c.2.1.size * Y.countP (pairTest n r s mx my c.1)).sum

end CFSG.Sporadic.Schreier.Native
