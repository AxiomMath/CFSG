module

public meta import Lean
public meta import Std.Data.HashMap
public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1ThreeInputs
public import CFSG.Certificates.Kernel.Common.Eval
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

namespace CertificateChecks.KernelCo1ThreeK.GenQ

open CFSG.KC.Eval CFSG.Sporadic.Co1Schreier.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T

meta def natsV (xs : List Nat) : Val := .list (xs.toArray.map .nat)

meta def nats : Val → Except String (Array Nat)
  | .list xs => xs.mapM fun | .nat n => pure n | _ => throw "qStep: expected a natural"
  | _ => throw "qStep: expected a list"

meta def natss : Val → Except String (Array (Array Nat))
  | .list xs => xs.mapM nats
  | _ => throw "qStep: expected a list of lists"

meta def addV (x y : Nat) : Nat := Id.run do
  let mut r := 0
  let mut x := x
  let mut y := y
  let mut b := 1
  for _ in [0:6] do
    r := r + b * ((x % 3 + y % 3) % 3)
    x := x / 3
    y := y / 3
    b := b * 3
  return r

meta def actV (rows : Array Nat) (v acc : Nat) : Nat := Id.run do
  let mut acc := acc
  let mut v := v
  for j in [0:rows.size] do
    for _ in [0:v % 3] do
      acc := addV acc rows[j]!
    v := v / 3
  return acc

meta def mulQ (A TT : Array (Array Nat)) (x y : Nat) : Nat :=
  let t := (TT[x / 729]!)[y / 729]!
  729 * (t / 729) + actV A[y / 729]! (x % 729) (addV (t % 729) (y % 729))

meta def eprod (A : Array Rows) (v : Nat) : Rows := Id.run do
  let mut acc := one ()
  let mut v := v
  for k in [0:6] do
    for _ in [0:v % 3] do
      acc := mul acc A[k]!
    v := v / 3
  return acc

public meta def qStep (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  if args.size != 4 then throw "qStep: expected CS.TR, CS.NR, CS.Q, CS.W"
  let A ← natss args[0]!
  let NR ← natss args[1]!
  let Q ← natss args[2]!
  let W ← nats args[3]!
  let B := #[NR[3]!, NR[4]!]
  let RL := Q.map fun q => 729 * (q[3]! / 2 - 12) + q[2]! / 8
  let mut TT : Array (Array Nat) := #[]
  for k in [0:27] do
    let mut row : Array Nat := #[729 * k]
    for l in [1:27] do
      let c := W[l]!
      let i := (c >>> 1) % 2 ^ 20 - 3
      let j := c >>> 21
      let t := row[i]!
      let r := RL[2 * (t / 729) + j]!
      row := row.push (729 * (r / 729) + actV A[r / 729]! (r % 729) (actV B[j]! (t % 729) 0))
    TT := TT.push row
  let mul' := mulQ A TT
  let cube := fun x => mul' (mul' x x) x
  let qc := fun j => let r := RL[j]!; 729 * (r / 729) + actV A[r / 729]! (r % 729) 0
  let GC : Array Nat := #[1, 3, 9, 27, 81, 243, qc 0, qc 1]
  let invQ := fun h => (List.range 19683).find? fun y => mul' h y == 0
  let GI ← GC.mapM fun h => match invQ h with | some y => pure y | none => throw "qStep: inverse"
  let L := (Native.lRows ()).toArray
  let Ar := L.extract 0 6
  let q6 := Native.wordL (Data.qGenWords.getD 6 [])
  let q7 := Native.wordL (Data.qGenWords.getD 7 [])
  let mut code : Std.HashMap Rows Nat := {}
  for v in [0:729] do
    code := code.insert (eprod Ar v) v
  let rowsOf := fun (g : Rows) => Id.run do
    let gi := inv g
    let mut r : Array Nat := #[]
    for j in [0:6] do
      match code.get? (mul (mul gi Ar[j]!) g) with
      | some c => r := r.push c
      | none => return none
    return some r
  let mut ts : Array Rows := #[one ()]
  for l in [1:27] do
    let c := W[l]!
    ts := ts.push (mul ts[(c >>> 1) % 2 ^ 20 - 3]! (if c >>> 21 == 0 then q6 else q7))
  for k in [0:27] do
    if rowsOf ts[k]! != some A[k]! then throw s!"qStep: action of t_{k}"
  let mut RP : Array Nat := #[]
  for i in [0:42] do
    let r := Native.repRows i
    let some rr := rowsOf r | throw s!"qStep: representative {i} outside N(E)"
    let some k := A.findIdx? (· == rr) | throw s!"qStep: representative {i} outside Q"
    let some v := code.get? (mul (inv ts[k]!) r) | throw s!"qStep: representative {i}"
    RP := RP.push (729 * k + v)
  let mut DPa : Array Nat := Array.replicate 19683 0
  let mut FTa : Array Nat := Array.replicate 19683 0
  let mut queue : Array Nat := #[]
  for x in RP do
    if DPa[x]! == 0 then
      DPa := DPa.set! x 1
      queue := queue.push x
  let mut qi := 0
  while qi < queue.size do
    let c := queue[qi]!
    for g in [0:8] do
      let x := mul' (mul' GC[g]! c) GI[g]!
      if DPa[x]! == 0 then
        DPa := DPa.set! x (DPa[c]! + 1)
        FTa := FTa.set! x (8 * c + g)
        queue := queue.push x
    qi := qi + 1
  let mut n3 := 0
  let mut dmax := 0
  for x in [729:19683] do
    let o3 := cube x == 0
    if o3 then n3 := n3 + 1
    if o3 != (DPa[x]! != 0) then throw s!"qStep: code {x} (order 3: {o3})"
    if DPa[x]! > 255 then throw "qStep: depth"
    dmax := max dmax DPa[x]!
  if n3 != 4374 then throw s!"qStep: {n3} codes of order 3 outside E"
  let DP := (List.range 19683).foldr (fun x acc => (acc <<< 8) ||| DPa[x]!) 0
  let FT := (List.range 26).map fun k => natsV ((List.range 729).map fun v => FTa[729 * (k + 1) + v]!)
  let ADT := (List.range 729).foldr (fun i acc => (acc <<< 5) ||| addV (i / 27) (i % 27)) 0
  let AT := (List.range 27).map fun l =>
    (List.range 729).foldr (fun v acc => (acc <<< 10) ||| actV A[l]! v 0) 0
  return #[(`ADT, .nat ADT), (`AT, natsV AT), (`RL, natsV RL.toList), (`TT, .list (TT.map fun r => natsV r.toList)),
    (`GC, natsV GC.toList), (`RP, natsV RP.toList), (`DP, .nat DP), (`FT, .list FT.toArray),
    (`ST, natsV [n3, dmax])]

end CertificateChecks.KernelCo1ThreeK.GenQ
