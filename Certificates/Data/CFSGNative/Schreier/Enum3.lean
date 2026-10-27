module

public import Certificates.Data.CFSGNative.Schreier.Check

public section

namespace CFSG.Certificates.Native

open CFSG.Monster.B.Co2.Native

@[expose] def tr3 (L : Array Level) (a b c p : Nat) : Nat :=
  L[0]!.tr[a]![L[1]!.tr[b]![L[2]!.tr[c]![p]!]!]!

@[expose] def isInv3 (L : Array Level) (n a b c : Nat) : Bool :=
  !(allLt n fun p => tr3 L a b c p == p) && allLt n fun p => tr3 L a b c (tr3 L a b c p) == p

@[expose] def moves3 (L : Array Level) (R : Array Nat) (a b c : Nat) : Bool :=
  !(allLt R.size fun k => tr3 L a b c R[k]! == R[k]!)

@[expose] def conjOK3 (L : Array Level) (n : Nat) (u : Array Nat) (a b c a' b' c' : Nat) : Bool :=
  allLt n fun p => tr3 L a' b' c' u[p]! == tr3 L a b c (tr3 L a' b' c' p)

@[expose] def prod3 (n : Nat) (L : Array Level) (a b c : Nat) : Array Nat :=
  Array.ofFn (n := n) fun p => tr3 L a b c p.val

@[expose] def coords3 (n : Nat) (L : Array Level) (base g : Array Nat) : Nat × Nat × Nat :=
  let a := L[0]!.pos[g[base[0]!]!]!
  let g₁ := compA n L[0]!.trInv[a]! g
  let b := L[1]!.pos[g₁[base[1]!]!]!
  let g₂ := compA n L[1]!.trInv[b]! g₁
  (a, b, L[2]!.pos[g₂[base[2]!]!]!)

@[expose] def idx3 (L : Array Level) (x : Nat × Nat × Nat) : Nat :=
  (x.1 * L[1]!.pts.size + x.2.1) * L[2]!.pts.size + x.2.2

@[expose] def conjSearch3 (n : Nat) (L : Array Level) (base : Array Nat)
    (gens us : Array (Array Nat)) : Array (Nat × Nat × Nat × Nat) := Id.run do
  let size := L[0]!.pts.size * L[1]!.pts.size * L[2]!.pts.size
  let gInv := gens.map (invCand n)
  let mut wit : Array (Nat × Nat × Nat × Nat) := Array.replicate size (0, 0, 0, 0)
  let mut seen : Array Bool := Array.replicate size false
  let mut queue : Array ((Nat × Nat × Nat) × Nat × (Nat × Nat × Nat)) := #[]
  for j in [0:us.size] do
    let x := coords3 n L base us[j]!
    let i := idx3 L x
    if !seen[i]! then
      seen := seen.set! i true
      wit := wit.set! i (j, 0, 0, 0)
      queue := queue.push (x, j, (0, 0, 0))
  let mut head := 0
  for _ in [0:size] do
    if head < queue.size then
      let (x, j, t) := queue[head]!
      head := head + 1
      let xa := prod3 n L x.1 x.2.1 x.2.2
      let ta := prod3 n L t.1 t.2.1 t.2.2
      for k in [0:gens.size] do
        let y := coords3 n L base (compA n gens[k]! (compA n xa gInv[k]!))
        let i := idx3 L y
        if !seen[i]! then
          let t' := coords3 n L base (compA n gens[k]! ta)
          seen := seen.set! i true
          wit := wit.set! i (j, t'.1, t'.2.1, t'.2.2)
          queue := queue.push (y, j, t')
  return wit

end CFSG.Certificates.Native
