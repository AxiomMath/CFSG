module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import Certificates.Data.TabCo1ThreeD
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

namespace CertificateChecks.KernelCo1B.Fix17590

open CFSG.KC.Eval

public meta def natV (v : Val) : Except String Nat :=
  match v with
  | .nat n => .ok n
  | _ => .error "expected a natural number"

public meta def rowsOfP (X : Nat) : Array Nat :=
  Array.ofFn (n := 24) fun i => (X >>> (24 * i.val)) &&& (2 ^ 24 - 1)

public meta def mulRw (X Y : Array Nat) : Array Nat :=
  X.map fun r => (List.range 24).foldl (fun acc j => if r.testBit j then acc ^^^ Y.getD j 0 else acc) 0

public meta def actRw (R : Array Nat) (v : Nat) : Nat :=
  (List.range 24).foldl (fun acc i =>
    let c := R.getD i 0 &&& v
    let par := (List.range 24).foldl (fun s b => if c.testBit b then !s else s) false
    if par then acc ||| (1 <<< i) else acc) 0

public meta def lowBit (v : Nat) : Nat := ((List.range 24).find? fun b => v.testBit b).getD 24

public meta def reduceP (piv : Array (Nat × Nat × Nat)) (z y : Nat) : Nat × Nat := Id.run do
  let mut z := z
  let mut y := y
  for _ in [0:25] do
    if z != 0 then
      match piv.find? (fun p => p.1 == lowBit z) with
      | some p =>
        z := z ^^^ p.2.1
        y := y ^^^ p.2.2
      | none => pure ()
  return (z, y)

public meta def fixStep (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  if args.size != 0 then throw "fixStep: expected no arguments"
  let C := CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeD.c1Rows ()
  let mut piv : Array (Nat × Nat × Nat) := #[]
  let mut ker : Array (Nat × Nat × Nat) := #[]
  for k in [0:24] do
    let e := 1 <<< k
    let (z, y) := reduceP piv (actRw C e ^^^ e) e
    if z != 0 then
      piv := piv.push (lowBit z, z, y)
    else
      let (f, _) := reduceP ker y 0
      ker := ker.push (lowBit f, f, 0)
  if piv.size + ker.size != 24 then throw "fixStep: wrong dimensions"
  return #[(`F, .list (ker.map fun p => .nat p.2.1)), (`Y, .list (piv.map fun p => .nat p.2.2))]

end CertificateChecks.KernelCo1B.Fix17590
