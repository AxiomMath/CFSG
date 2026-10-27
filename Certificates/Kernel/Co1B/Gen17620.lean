module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import Certificates.Data.TabCo1ThreeA
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

namespace CertificateChecks.KernelCo1B.Bound17620

open CFSG.KC.Eval CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeA
  CFSG.HardMathSupport.Dickson.I271.TabCo1 CFSG.Sporadic.Co1Schreier.Native
  CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1.TwoBNative

public meta def kDagA : List Rows × List Rows × Bool := kDag ext

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
    (conds : List (List Cond)) (cnts : List Nat) : Except String (Array (Lean.Name × Val)) := do
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
  if SL.size == 0 || CF.size == 0 then throw "boundValsP: no levels"
  match SL[0]! with
  | .list a => if a.size != 0 then throw "boundValsP: level 0 has selected conditions"
  | _ => throw "boundValsP: level 0"
  return #[(`Sel, .list SL), (`CFt, .list (CF.extract 1 CF.size)), (`CNs, .list CN),
    (`NP, .list NP)]

public meta def stepA (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  if args.size != 0 then throw "stepA: expected no arguments"
  let D := kDag ext
  if !D.2.2 then throw "stepA: inverse checks"
  let cs := colsOf (powList (nd D 95) 3)
  let words := chainDerivs () ++ ext
  return #[(`KW, .list (words.toArray.map fun w => natsV (w.map encL))),
    (`T, .list (cs.map fun c => .nat (packB c)))] ++
    (← boundValsP (xsSet ()) cs base conds cnts)

end CertificateChecks.KernelCo1B.Bound17620
