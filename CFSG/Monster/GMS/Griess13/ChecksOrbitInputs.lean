module

public import CFSG.Monster.GMS.Griess13.Data

@[expose] public section

namespace CFSG.Monster.GMS.Griess13.Co1Data

open scoped Matrix

def codeOf (v : Fin 6 → ZMod 3) : ℕ := ∑ i : Fin 6, (v i).val * 3 ^ i.val

def vecOfCode (c : ℕ) : Fin 6 → ZMod 3 := fun i => ((c / 3 ^ i.val % 3 : ℕ) : ZMod 3)

def matN (s : Fin 2) : Array (Array ℕ) :=
  Array.ofFn fun i : Fin 6 => Array.ofFn fun j : Fin 6 => (actN s i j).val

def stepN (A : Array (Array ℕ)) (c : ℕ) : ℕ :=
  (List.range 6).foldl (fun acc i =>
    acc + 3 ^ i * ((List.range 6).foldl (fun t j => t + (A[i]!)[j]! * (c / 3 ^ j % 3)) 0 % 3)) 0

def matNs : Array (Array (Array ℕ)) := #[matN 0, matN 1]

def stepS (s c : ℕ) : ℕ := stepN (matNs[s]!) c

def orbitBFS (reps : List ℕ) : Array ℕ × Array ℕ × Array ℕ × Array ℕ := Id.run do
  let mut cls : Array ℕ := Array.replicate 729 0
  let mut dist : Array ℕ := Array.replicate 729 0
  let mut par : Array ℕ := Array.replicate 729 0
  let mut gen : Array ℕ := Array.replicate 729 0
  let mut queue : Array ℕ := #[]
  let mut k := 1
  for r in reps do
    cls := cls.set! r k
    queue := queue.push r
    k := k + 1
  let mut head := 0
  while head < queue.size do
    let c := queue[head]!
    head := head + 1
    for s in [0, 1] do
      let d := stepS s c
      if cls[d]! == 0 then
        cls := cls.set! d cls[c]!
        dist := dist.set! d (dist[c]! + 1)
        par := par.set! d c
        gen := gen.set! d s
        queue := queue.push d
  return (cls, dist, par, gen)

def repVec (k : ℕ) : Fin 6 → ZMod 3 := if k = 1 then w1 else if k = 2 then wB else wC

def repCode (k : ℕ) : ℕ := codeOf (repVec k)

def orbTab : Array ℕ × Array ℕ × Array ℕ × Array ℕ :=
  orbitBFS [repCode 1, repCode 2, repCode 3]

def orbitClass (w : Fin 6 → ZMod 3) : ℕ := orbTab.1[codeOf w]!

def orbCheck : Bool :=
  (List.range 729).all fun c => c == 0 ||
    ((orbTab.1[c]! == 1 || orbTab.1[c]! == 2 || orbTab.1[c]! == 3) &&
      (if c == repCode orbTab.1[c]! then orbTab.2.1[c]! == 0 else
        decide (0 < orbTab.2.2.1[c]!) && decide (orbTab.2.2.1[c]! < 729) &&
        decide (orbTab.2.2.2[c]! < 2) &&
        stepS orbTab.2.2.2[c]! orbTab.2.2.1[c]! == c &&
        orbTab.1[orbTab.2.2.1[c]!]! == orbTab.1[c]! &&
        decide (orbTab.2.1[orbTab.2.2.1[c]!]! < orbTab.2.1[c]!)))

def orbitIndex (w : Fin 6 → ZMod 3) : Fin 3 :=
  if orbitClass w = 1 then 0 else if orbitClass w = 2 then 1 else 2

end CFSG.Monster.GMS.Griess13.Co1Data
