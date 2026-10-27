module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import Certificates.Data.TabCo1ThreeD
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

namespace CertificateChecks.KernelCo1B.Bound17591

open CFSG.KC.Eval CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeD
  CFSG.HardMathSupport.Dickson.I271.TabCo1 CFSG.Sporadic.Co1Schreier.Native
  CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Block

public meta def packB (X : Array Nat) : Nat :=
  (List.range 24).foldl (fun acc i => acc ||| ((X.getD i 0 % 2 ^ 24) <<< (24 * i))) 0

public meta def boundStep (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  if args.size != 0 then throw "boundStep: expected no arguments"
  let c1 := c1Rows ()
  let cs := colsOf (powList c1 3)
  let xs := xsSet ()
  let mut G : Array (Array Nat) := Array.replicate 4096 #[]
  for i in [0:certVecs.size] do
    let x := certVecs[i]!
    G := G.modify (x >>> 12) (·.push ((x &&& 4095) + 4096 * i))
  let CF := (List.range base.length).map fun i =>
    let b := base.take i
    let u := base.getD i 0
    (conds.getD i []).map fun c =>
      let fv := fN cs b c.2
      typN xs (combN cs c.1 fv u) :: fv :: c.1
  let CN := (List.range base.length).map fun i =>
    let b := base.take i
    let u := base.getD i 0
    let ok := fun x => (conds.getD i []).all fun c =>
      typN xs (combN cs c.1 (fN cs b c.2) x) == typN xs (combN cs c.1 (fN cs b c.2) u)
    (List.range 9).map fun c =>
      ((List.range (13 * 840)).filter fun k => ok certVecs[13 * 840 * c + k]!).length
  return #[(`T, .list ((List.range 3).toArray.map fun a => .nat (packB (cs.getD a #[])))),
    (`CN, .list (CN.toArray.map fun l => .list (l.toArray.map .nat))),
    (`G, .list (G.map fun g => .list (g.map .nat))),
    (`CF, .list (CF.toArray.map fun l => .list (l.toArray.map fun c => .list (c.toArray.map .nat))))]

end CertificateChecks.KernelCo1B.Bound17591
