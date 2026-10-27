module

public import Certificates.Data.SmithL6Orbit
public import Std.Data.HashSet

public section

namespace CFSG.SmithL6

@[expose] def pairStabGens (_ : Unit := ()) : Array Nat :=
  (Array.range 1953).filter fun g => tvImg g 0 == 0

@[expose] def isPartner (u : Nat) : Bool := u != 0 && tvImg 0 u == tvImg u 0

@[expose] def chkPartners : Bool :=
  let G := pairStabGens ()
  isPartner 31 &&
  treeOK 1953 G.size (fun v => v == 31 || !isPartner v)
    (fun g u v => tvImg G[g]! u == v && (!isPartner v || isPartner u))
    (treeBFS 1953 (Array.range G.size) (fun g u => tvImg G[g]! u) [31])

@[expose] def fourGens (_ : Unit := ()) : Array Nat :=
  (Array.range 1953).filter fun g => tvImg g 0 == 0 && tvImg g 31 == 31

@[expose] def fourBase : Nat × Nat × Nat := (1352, 968, 1480)

@[expose] def fourStep (g : Nat) (t : Nat × Nat × Nat) : Nat × Nat × Nat :=
  (tvImg g t.1, tvImg g t.2.1, tvImg g t.2.2)

@[expose] def fourKey (t : Nat × Nat × Nat) : Nat := t.1 + 1953 * (t.2.1 + 1953 * t.2.2)

@[expose] def fourBfs (_ : Unit := ()) : Array (Nat × Nat × Nat) × Array Nat × Array Nat :=
  Id.run do
    let gens := fourGens ()
    let rows : Array (Array Nat) := gens.map fun g => Array.ofFn (n := 1953) fun a => tvImg g a.val
    let mut nodes : Array (Nat × Nat × Nat) := #[fourBase]
    let mut par : Array Nat := #[0]
    let mut lab : Array Nat := #[0]
    let mut seen : Std.HashSet Nat := (Std.HashSet.emptyWithCapacity 32768).insert (fourKey fourBase)
    let mut head := 0
    for _ in [0:25000] do
      if head < nodes.size then
        let t := nodes[head]!
        for i in [0:gens.size] do
          let row := rows[i]!
          let u : Nat × Nat × Nat := (row[t.1]!, row[t.2.1]!, row[t.2.2]!)
          if !seen.contains (fourKey u) then
            seen := seen.insert (fourKey u)
            nodes := nodes.push u
            par := par.push head
            lab := lab.push gens[i]!
        head := head + 1
    return (nodes, par, lab)

@[expose] def strictInc : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: t => decide (a < b) && strictInc (b :: t)

@[expose] def fourCheck (D : Array (Nat × Nat × Nat) × Array Nat × Array Nat) : Bool :=
  decide (D.1.size = 20160) && D.1[0]! == fourBase &&
  (List.range 20160).all (fun n =>
    decide (D.1[n]!.1 < 1953) && decide (D.1[n]!.2.1 < 1953) && decide (D.1[n]!.2.2 < 1953)) &&
  (List.range 20160).all (fun n => n == 0 ||
    (decide (D.2.1[n]! < n) && decide (D.2.2[n]! < 1953) && tvImg D.2.2[n]! 0 == 0 &&
      tvImg D.2.2[n]! 31 == 31 && D.1[n]! == fourStep D.2.2[n]! D.1[D.2.1[n]!]!)) &&
  strictInc ((D.1.toList.map fourKey).mergeSort (fun a b => decide (a ≤ b)))

@[expose] def chkFour : Bool := fourCheck (fourBfs ())

end CFSG.SmithL6
