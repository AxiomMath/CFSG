module

public import Certificates.Data.CFSGNative.MonsterB.Co2Chain

public section

namespace CFSG.Sporadic.Co2Rank3.Native

open CFSG.Monster.B.Co2.Native

@[expose] def orbitSearch (n : Nat) (gens : Array (Array Nat)) :
    Array Nat × Array Nat × Array Nat × Array Nat := Id.run do
  let mut lab : Array Nat := Array.replicate n n
  let mut dep : Array Nat := Array.replicate n 0
  let mut par : Array Nat := Array.replicate n 0
  let mut via : Array Nat := Array.replicate n 0
  for r in [0:n] do
    if dep[r]! == 0 then
      lab := lab.set! r r
      dep := dep.set! r 1
      let mut q : Array Nat := #[r]
      let mut head := 0
      for _ in [0:n] do
        if head < q.size then
          let x := q[head]!
          head := head + 1
          for k in [0:gens.size] do
            let y := (gens[k]!)[x]!
            if decide (y < n) && dep[y]! == 0 then
              lab := lab.set! y r
              dep := dep.set! y (dep[x]! + 1)
              par := par.set! y x
              via := via.set! y k
              q := q.push y
        else
          break
  return (lab, dep, par, via)

@[expose] def orbitsOK (n : Nat) (gens : Array (Array Nat)) (lab dep par via : Array Nat) :
    Bool :=
  allLt gens.size (fun k => allLt n fun x =>
      decide ((gens[k]!)[x]! < n) && lab[(gens[k]!)[x]!]! == lab[x]!) &&
    allLt n fun x => decide (lab[x]! < n) &&
      (if dep[x]! == 1 then lab[x]! == x else
        decide (par[x]! < n) && dep[par[x]!]! + 1 == dep[x]! && decide (via[x]! < gens.size) &&
          (gens[via[x]!]!)[par[x]!]! == x)

@[expose] def labelsOK (n : Nat) (lab : Array Nat) (roots : List (Nat × Nat)) : Bool :=
  allLt n (fun x => roots.any fun r => r.1 == lab[x]!) && roots.all fun r => lab[r.1]! == r.1

@[expose] def listLabelOK (n : Nat) (l : List Nat) (lab : Array Nat) (good : List Nat) : Bool :=
  allLt n fun x => l.contains x == good.contains lab[x]!

@[expose] def colourLabelOK (n : Nat) (c lab : Array Nat) (roots : List Nat) : Bool :=
  allLt n (fun x => c[x]! == c[lab[x]!]!) &&
    allLt roots.length fun i => allLt roots.length fun j =>
      i == j || c[roots.getD i 0]! != c[roots.getD j 0]!

end CFSG.Sporadic.Co2Rank3.Native
