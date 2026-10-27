module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import Certificates.Data.TabCo1ThreeC
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

namespace CertificateChecks.KernelCo1B.Bound17329

open CFSG.KC.Eval CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeC
  CFSG.HardMathSupport.Dickson.I271.TabCo1 CFSG.Sporadic.Co1Schreier.Native
  CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1.TwoBNative

public meta def kDagC : List Rows × List Rows × Bool := kDag ext

meta def encLC (l : Int) : Nat := if 0 < l then 2 * l.toNat else 2 * (-l).toNat + 1

meta def natsVC (xs : List Nat) : Val := .list (xs.toArray.map .nat)

meta def packC (X : Array Nat) : Nat :=
  (List.range 24).foldl (fun acc i => acc ||| ((X.getD i 0 % 2 ^ 24) <<< (24 * i))) 0

meta partial def greedySelC (pass : Array (Array Bool)) (cnt : Nat) (alive sel : Array Nat) :
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
    if n == alive.size then throw "greedySelC: no condition removes a vector"
    greedySelC pass cnt (alive.filter fun k => (pass[j]!)[k]!) (sel.push j)
  | none => throw "greedySelC: conditions exhausted above the count"

meta def boundValsC (xs : Std.HashSet Nat) (cs : Array (Array Nat)) (base : List Nat)
    (nfix : Nat) (conds : List (List Cond)) (cnts : List Nat) (sfx : String) :
    Except String (Array (Lean.Name × Val)) := do
  if certVecs.size != 9 * 13 * 840 then throw "boundValsC: |X| ≠ 98280"
  let mut SL : Array Val := #[]
  let mut CF : Array Val := #[]
  let mut CN : Array Val := #[]
  let mut NP : Array Val := #[]
  for i in [0:base.length] do
    if i < nfix then
      SL := SL.push (.list #[])
      CN := CN.push (natsVC (List.replicate 9 0))
      NP := NP.push (.nat 1)
      continue
    let b := base.take i
    let u := base.getD i 0
    let cl := (conds.getD i []).toArray
    let pass := cl.map fun c =>
      let fv := fN cs b c.2
      let tu := typN xs (combN cs c.1 fv u)
      certVecs.map fun x => typN xs (combN cs c.1 fv x) == tu
    let sel ← greedySelC pass (cnts.getD i 0) (Array.range certVecs.size) #[]
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
  return #[(Lean.Name.mkSimple ("T" ++ sfx), .list (cs.map fun c => .nat (packC c))),
    (Lean.Name.mkSimple ("Sel" ++ sfx), .list SL),
    (Lean.Name.mkSimple ((if nfix = 0 then "CFs" else "CFsT") ++ sfx), .list CF),
    (Lean.Name.mkSimple ("CNs" ++ sfx), .list CN),
    (Lean.Name.mkSimple ("NP" ++ sfx), .list NP)]

public meta def stepC (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  if args.size != 0 then throw "stepC: expected no arguments"
  let D := kDag ext
  if !D.2.2 then throw "stepC: inverse checks"
  let xR := rootRows3C ()
  let QG := #[nd D 88, nd D 89, nd D 90, nd D 91]
  let Qt := gtBFS QG 300
  let xs := xsSet ()
  let words := chainDerivs () ++ ext
  return #[(`KW, .list (words.toArray.map fun w => natsVC (w.map encLC)))] ++
    (← boundValsC xs (colsOf (powList xR 3)) base 6 conds cnts "") ++
    (← boundValsC xs (colsOf Qt.pts.toList) base2 0 conds2 cnts2 "2")

end CertificateChecks.KernelCo1B.Bound17329
