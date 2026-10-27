module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1ThreeInputs
public meta import Certificates.Data.TabCo1ThreeB
public meta import Certificates.Data.TabCo1ThreeE
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

namespace CertificateChecks.KernelCo1ThreeK.GenZ

open CFSG.KC.Eval CFSG.Sporadic.Co1Schreier.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T

public meta def kDagZ : List Rows × List Rows × Bool :=
  CFSG.HardMathSupport.Dickson.I271.TabCo1.kDag CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeB.ext

meta def encL (l : Int) : Nat := if 0 < l then 2 * l.toNat else 2 * (-l).toNat + 1

meta def eprod (A : Array Rows) (v : Nat) : Rows := Id.run do
  let mut acc := one ()
  let mut v := v
  for k in [0:6] do
    for _ in [0:v % 3] do
      acc := mul acc A[k]!
    v := v / 3
  return acc

meta def natsV (xs : List Nat) : Val := .list (xs.toArray.map .nat)

public meta def zStep (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  if args.size != 0 then throw "zStep: expected no arguments"
  let A := ((Native.lRows ()).toArray).extract 0 6
  let DE := CFSG.HardMathSupport.Dickson.I271.TabCo1.kDag
    CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeE.ext
  if !DE.2.2 || !kDagZ.2.2 then throw "zStep: inverse checks"
  let n := DE.1.getD 87 (one ())
  let ni := DE.2.1.getD 87 (one ())
  let z := kDagZ.1.getD 90 (one ())
  let y := mul (mul ni z) n
  let some v := (List.range 729).find? (fun v => eprod A v == y) | throw "zStep: n⁻¹ z n ∉ E"
  let words := CFSG.HardMathSupport.Dickson.I271.TabCo1.chainDerivs () ++
    CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeB.ext
  return #[(`KW, .list (words.toArray.map fun w => natsV (w.map encL))), (`V, .nat v)]

end CertificateChecks.KernelCo1ThreeK.GenZ
