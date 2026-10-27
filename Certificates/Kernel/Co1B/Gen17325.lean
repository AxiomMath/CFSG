module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import Certificates.Data.TabCo1FiveB
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

namespace CertificateChecks.KernelCo1B.Bound17325

open CFSG.KC.Eval CFSG.HardMathSupport.Dickson.I271.TabCo1FiveB
  CFSG.HardMathSupport.Dickson.I271.TabCo1 CFSG.Sporadic.Co1Schreier.Native
  CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1.TwoBNative

public meta def kDagB : List Rows × List Rows × Bool := kDag ext

meta def encL (l : Int) : Nat := if 0 < l then 2 * l.toNat else 2 * (-l).toNat + 1

meta def natsV (xs : List Nat) : Val := .list (xs.toArray.map .nat)

meta def packB (X : Array Nat) : Nat :=
  (List.range 24).foldl (fun acc i => acc ||| ((X.getD i 0 % 2 ^ 24) <<< (24 * i))) 0

meta partial def greedySel (pass : Array (Array Bool)) (cnt : Nat) (alive sel : Array Nat) :
    Except String (Array Nat) := do
  if alive.size ≤ cnt then return sel
  let mut best : Option (Nat × Nat) := none
  for j in [0:pass.size] do
    if !sel.contains j then
      let n := (alive.filter fun k => (pass[j]!)[k]!).size
      match best with
      | some (_, m) => if n < m then best := some (j, n)
      | none => best := some (j, n)
  match best with
  | some (j, n) =>
    if n == alive.size then throw "greedySel: no condition removes a vector"
    greedySel pass cnt (alive.filter fun k => (pass[j]!)[k]!) (sel.push j)
  | none => throw "greedySel: conditions exhausted above the count"

meta def boundValsP (xs : Std.HashSet Nat) (cs : Array (Array Nat)) (base : List Nat)
    (conds : List (List Cond)) (cnts : List Nat) (sfx : String) :
    Except String (Array (Lean.Name × Val)) := do
  if certVecs.size != 9 * 13 * 840 then throw "boundValsP: |X| ≠ 98280"
  let mut SL : Array Val := #[]
  let mut CF : Array Val := #[]
  let mut CN : Array Val := #[]
  let mut NP : Array Val := #[]
  for i in [0:base.length] do
    let b := base.take i
    let u := base.getD i 0
    let cl := (conds.getD i []).toArray
    let pass := cl.map fun c =>
      let fv := fN cs b c.2
      let tu := typN xs (combN cs c.1 fv u)
      certVecs.map fun x => typN xs (combN cs c.1 fv x) == tu
    let sel ← greedySel pass (cnts.getD i 0) (Array.range certVecs.size) #[]
    SL := SL.push (.list (sel.map .nat))
    CF := CF.push (.list (sel.map fun j =>
      let c := cl[j]!
      let fv := fN cs b c.2
      .list (((typN xs (combN cs c.1 fv u)) :: fv :: c.1).toArray.map .nat)))
    let ok := fun k => sel.all fun j => (pass[j]!)[k]!
    CN := CN.push (.list ((Array.range 9).map fun blk =>
      .nat ((Array.range (13 * 840)).filter fun k => ok (13 * 840 * blk + k)).size))
    let mut alive := Array.range certVecs.size
    let mut np := 0
    for j in sel do
      if np == 0 || alive.size ≥ 2000 then
        np := np + 1
        alive := alive.filter fun k => (pass[j]!)[k]!
    NP := NP.push (.nat np)
  return #[(Lean.Name.mkSimple ("T" ++ sfx), .list (cs.map fun c => .nat (packB c))),
    (Lean.Name.mkSimple ("Sel" ++ sfx), .list SL),
    (Lean.Name.mkSimple ("CFs" ++ sfx), .list CF),
    (Lean.Name.mkSimple ("CNs" ++ sfx), .list CN),
    (Lean.Name.mkSimple ("NP" ++ sfx), .list NP)]

meta def commWit (P : Array Rows) (t : Rows) : Except String (Nat × Nat) := do
  for a in [0:P.size] do
    for b in [0:P.size] do
      if mul (mul P[a]! P[b]!) (mul (inv P[a]!) (inv P[b]!)) == t then return (a, b)
  throw "commWit: not a commutator of points"

public meta def stepB (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  if args.size != 0 then throw "stepB: expected no arguments"
  let D := kDag ext
  if !D.2.2 then throw "stepB: inverse checks"
  let kR := nd D 88
  let x1R := nd D 89
  let y1R := nd D 90
  let tR := nd D 91
  let tI := ndI D 91
  let Lt := gtBFS #[x1R, y1R] 200
  let (a1, b1) ← commWit Lt.pts x1R
  let (a2, b2) ← commWit Lt.pts y1R
  let xs := xsSet ()
  let words := chainDerivs () ++ ext
  return #[(`KW, .list (words.toArray.map fun w => natsV (w.map encL))), (`D1, .nat (packB repD1)),
    (`LI, .list (Lt.pts.map fun p => .nat (packB (inv p)))), (`CW, natsV [a1, b1, a2, b2])] ++
    (← boundValsP xs (colsOf (powList kR 5)) base conds cnts "") ++
    (← boundValsP xs (colsOf (ptRowsB kR x1R y1R tR tI)) base2 conds2 cnts2 "2")

end CertificateChecks.KernelCo1B.Bound17325
