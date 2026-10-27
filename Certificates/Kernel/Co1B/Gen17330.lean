module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import Certificates.Data.TabCo1ThreeB
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

namespace CertificateChecks.KernelCo1B.Bound17330

open CFSG.KC.Eval CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeB
  CFSG.HardMathSupport.Dickson.I271.TabCo1 CFSG.Sporadic.Co1Schreier.Native
  CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Block

meta def packB (X : Array Nat) : Nat :=
  (List.range 24).foldl (fun acc i => acc ||| ((X.getD i 0 % 2 ^ 24) <<< (24 * i))) 0

meta def boundVals (xs : Std.HashSet Nat) (cs : Array (Array Nat)) (base : List Nat)
    (conds : List (List Cond)) (sfx : String) : Array (Lean.Name × Val) :=
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
  #[(Lean.Name.mkSimple ("T" ++ sfx), .list (cs.map fun c => .nat (packB c))),
    (Lean.Name.mkSimple ("CN" ++ sfx), .list (CN.toArray.map fun l => .list (l.toArray.map .nat))),
    (Lean.Name.mkSimple ("CF" ++ sfx),
      .list (CF.toArray.map fun l => .list (l.toArray.map fun c => .list (c.toArray.map .nat))))]

public meta def boundStep (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  if args.size != 0 then throw "boundStep: expected no arguments"
  let D := kDag ext
  let aR := nd D 88
  let bR := nd D 89
  let xR := nd D 90
  let zR := nd D 91
  let xs := xsSet ()
  return boundVals xs (colsOf (powList xR 3)) base conds "" ++
    boundVals xs (colsOf (ptRows3B aR bR xR zR)) base2 conds2 "2"

end CertificateChecks.KernelCo1B.Bound17330
