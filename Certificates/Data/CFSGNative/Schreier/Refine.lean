module

public import Certificates.Data.CFSGNative.Schreier.SetOrbit

public section

namespace CFSG.Certificates.Native

open CFSG.Monster.B.Co2.Native

@[expose] def sigCode (a : Nat) (l : List Nat) : Nat :=
  l.foldl (fun h x => (h * 1000003 + x + 1) % 4398046511093) ((a + 7) % 4398046511093)

@[expose] def nbrColours (nbr : Array (List Nat)) (c : Array Nat) (v : Nat) : List Nat :=
  ((nbr[v]!).map fun w => c[w]!).mergeSort fun a b => decide (a ≤ b)

@[expose] def refineStep (n : Nat) (nbr : Array (List Nat)) (c : Array Nat) : Array Nat :=
  Array.ofFn (n := n) fun v => sigCode c[v.val]! (nbrColours nbr c v.val)

@[expose] def refineIter (n : Nat) (nbr : Array (List Nat)) (c : Array Nat) : Nat → Array Nat
  | 0 => c
  | k + 1 => refineStep n nbr (refineIter n nbr c k)

@[expose] def individualize (n : Nat) (b : List Nat) (s : Nat) : Array Nat :=
  Array.ofFn (n := n) fun v => match (b.take s).idxOf? v.val with
    | some j => j + 1
    | none => 0

@[expose] def classSize (c : Array Nat) (v : Nat) : Nat :=
  c.toList.count c[v]!

@[expose] def strictIncr : List Nat → Bool
  | a :: b :: l => decide (a < b) && strictIncr (b :: l)
  | _ => true

@[expose] def adjOK (n : Nat) (gens : Array (Array Nat)) (nbr : Array (List Nat))
    (root : List Nat) : Bool :=
  nbr.size == n && nbr[0]! == root &&
    allLt n (fun x => (nbr[x]!).all (fun y => decide (y < n)) && strictIncr nbr[x]!) &&
    (nbr[0]!).all (fun y => (nbr[y]!).contains 0) &&
    allLt gens.size (fun k => allLt n fun x =>
      nbr[(gens[k]!)[x]!]! == imgSorted gens[k]! nbr[x]!)

@[expose] def adjSearch (n : Nat) (gens : Array (Array Nat)) (root : List Nat) :
    Array (List Nat) := Id.run do
  let mut nbr : Array (List Nat) := Array.replicate n []
  let mut seen : Array Bool := Array.replicate n false
  nbr := nbr.set! 0 root
  seen := seen.set! 0 true
  let mut queue : Array Nat := #[0]
  let mut head := 0
  for _ in [0:n] do
    if head < queue.size then
      let x := queue[head]!
      head := head + 1
      for k in [0:gens.size] do
        let y := (gens[k]!)[x]!
        if !seen[y]! then
          seen := seen.set! y true
          nbr := nbr.set! y (imgSorted gens[k]! nbr[x]!)
          queue := queue.push y
  return nbr

end CFSG.Certificates.Native
