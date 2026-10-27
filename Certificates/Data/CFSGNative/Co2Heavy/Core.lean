module

public import Certificates.Data.CFSGNative.Co2Rank.Dfs
public import Std.Data.HashMap

public section

namespace CFSG.Sporadic.Co2Heavy.Native

open CFSG.Sporadic.Co2Rank CFSG.Sporadic.SmallF2.Native

set_option compiler.extract_closed false

@[expose] def sqIdxN (n : Nat) (el : Array (Array Nat)) : Array Nat :=
  (Array.range n).filter fun k => mulRows 22 el[k]! el[k]! == idRows 22

@[expose] def partnersN (el : Array (Array Nat)) (sq : Array Nat) (X : Array Nat) : Nat :=
  (sq.filter fun k => commRows el[k]! X).size

@[expose] def heavyCheckN (c n : Nat) (el : Array (Array Nat)) (sq reps : Array Nat)
    (wit : Array (Option (Nat × Nat))) : Bool :=
  reps.all (fun r => decide (r < n) && decide (partnersN el sq el[r]! < c)) &&
    wit.size == sq.size &&
    (List.range sq.size).all (fun i =>
      match wit[i]! with
      | some (s, j) => decide (s < n) && decide (j < reps.size) &&
          mulRows 22 el[s]! el[sq[i]!]! == mulRows 22 el[reps[j]!]! el[s]!
      | none => true) &&
    decide ((wit.filter Option.isNone).size < c)

@[expose] def invRowsPowN (g : Array Nat) : Array Nat := Id.run do
  let mut p := g
  for _ in [0:64] do
    if mulRows 22 p g == idRows 22 then return p
    p := mulRows 22 p g
  return p

@[expose] def heavyDataN (c : Nat) (el tbl : Array (Array Nat)) (pos : Std.HashMap (Array Nat) Nat)
    (sq : Array Nat) (gens : Array (Array Nat)) : Array Nat × Array (Option (Nat × Nat)) :=
  Id.run do
  let ginv := gens.map invRowsPowN
  let mut posSq : Std.HashMap Nat Nat := ∅
  for i in [0:sq.size] do
    posSq := posSq.insert sq[i]! i
  let mut wit : Array (Option (Nat × Nat)) := Array.replicate sq.size none
  let mut done : Array Bool := Array.replicate sq.size false
  let mut reps : Array Nat := #[]
  for i in [0:sq.size] do
    if !done[i]! then
      let k := sq[i]!
      let light := decide (partnersN el sq el[k]! < c)
      let j := reps.size
      if light then
        reps := reps.push k
        wit := wit.set! i (some (0, j))
      done := done.set! i true
      let mut queue : Array (Nat × Nat) := #[(k, 0)]
      let mut h := 0
      for _ in [0:sq.size + 1] do
        if h < queue.size then
          let (x, s) := queue[h]!
          h := h + 1
          for t in [0:gens.size] do
            let y := mulRows 22 (mulRows 22 ginv[t]! el[x]!) gens[t]!
            let ky := pos.getD y 0
            let s' := (tbl[s]!)[t]!
            match posSq.get? ky with
            | some iy =>
              if !done[iy]! then
                done := done.set! iy true
                if light then wit := wit.set! iy (some (s', j))
                queue := queue.push (ky, s')
            | none => pure ()
  return (reps, wit)

end CFSG.Sporadic.Co2Heavy.Native
