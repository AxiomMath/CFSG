module

public import Certificates.Data.GH23Perm
public import Certificates.Data.GH23Data

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.GH23Data

structure MemTab where
  gens : List Nat
  elems : List Nat
  tab : Std.HashSet Nat

@[expose] def memTab (gens : List Nat) : Option MemTab :=
  match closData gens with
  | none => none
  | some (E, T) => some ⟨gens, E, T⟩

@[expose] def memTabs (ms : List MemberData) : Option (List MemTab) :=
  ms.mapM fun m => memTab m.gens

@[expose] def dcWitness (P : MemTab) (A : List Nat) : Std.HashMap Nat (Nat × Nat × Nat) :=
  Id.run do
    let ga := P.gens.toArray
    let mut wit : Std.HashMap Nat (Nat × Nat × Nat) := {}
    for r in A do
      if !wit.contains r then
        wit := wit.insert r (r, oneC, oneC)
        let mut queue : Array Nat := #[r]
        let mut i := 0
        while i < queue.size do
          let x := queue[i]!
          let (_, p, q) := wit[x]!
          for g in ga do
            let y := mulC g x
            if !wit.contains y then
              wit := wit.insert y (r, mulC g p, q)
              queue := queue.push y
            let z := mulC x g
            if !wit.contains z then
              wit := wit.insert z (r, p, mulC q g)
              queue := queue.push z
          i := i + 1
    return wit

@[expose] def joinOK (mts : List MemTab) (P : MemTab) (r : Nat) : Bool :=
  P.tab.contains r ||
    (validC r &&
      (let gs := P.gens ++ [r]
       match replay gs (bfsChain gs) (({} : Std.HashSet Nat).insert oneC) with
       | none => false
       | some s => mts.any fun Q =>
           P.gens.all Q.tab.contains && Q.tab.contains r && Q.gens.all s.contains))

@[expose] def coverAll (mts : List MemTab) (P : MemTab)
    (wit : Std.HashMap Nat (Nat × Nat × Nat)) : List Nat → Std.HashSet Nat → Bool
  | [], _ => true
  | h :: rest, done =>
    match wit[h]? with
    | none => false
    | some (r, p, q) =>
      P.tab.contains p && P.tab.contains q && mulC (mulC p r) q == h &&
        (done.contains r || joinOK mts P r) && coverAll mts P wit rest (done.insert r)

@[expose] def stepOK (A : List Nat) (mts : List MemTab) (P : MemTab) : Bool :=
  coverAll mts P (dcWitness P A) A {}

@[expose] def latticeBody (A : List Nat) (mts : List MemTab) : Bool := mts.all (stepOK A mts)

end CFSG.OddStandard.SmallF3.HarrisU33.GH23Data
