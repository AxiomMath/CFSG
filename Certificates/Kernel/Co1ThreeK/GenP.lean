module

public meta import Lean
public meta import Std.Data.HashMap
public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1ThreeInputs
public meta import Certificates.Data.TabCo1ThreeE
public import Certificates.Kernel.Sporadic.RawGen
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

namespace CertificateChecks.KernelCo1ThreeK.Gen

open CFSG.KC.Eval CFSG.Sporadic.Co1Schreier.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T

public meta def kDagD : List Rows × List Rows × Bool :=
  CFSG.HardMathSupport.Dickson.I271.TabCo1.kDag CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeE.ext

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

public meta def pStep (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  if args.size != 0 then throw "pStep: expected no arguments"
  let L := (Native.lRows ()).toArray
  let A := L.extract 0 6
  let q6 := Native.wordL (Data.qGenWords.getD 6 [])
  let q7 := Native.wordL (Data.qGenWords.getD 7 [])
  let qs := #[q6, q7]
  let mut code : Std.HashMap Rows Nat := {}
  for v in [0:729] do
    code := code.insert (eprod A v) v
  if code.size != 729 then throw "pStep: the 729 products are not distinct"
  let rowsOf := fun (g : Rows) => Id.run do
    let gi := inv g
    let mut r : Array Nat := #[]
    for j in [0:6] do
      match code.get? (mul (mul gi A[j]!) g) with
      | some c => r := r.push c
      | none => return none
    return some r.toList
  let some r0 := rowsOf (one ()) | throw "pStep: identity"
  let mut ts : Array Rows := #[one ()]
  let mut acts : Array (List Nat) := #[r0]
  let mut recs : Array Nat := #[2 * (2 + 2 ^ 20 * 2)]
  let mut i := 0
  while i < ts.size do
    for j in [0:2] do
      let x := mul ts[i]! qs[j]!
      let some r := rowsOf x | throw "pStep: not in the normalizer"
      if !acts.contains r then
        ts := ts.push x
        acts := acts.push r
        recs := recs.push (2 * ((3 + i) + 2 ^ 20 * j))
    i := i + 1
  if ts.size != 27 then throw s!"pStep: {ts.size} actions"
  let mut eqs : Array Val := #[]
  for k in [0:27] do
    for j in [0:2] do
      let x := mul ts[k]! qs[j]!
      let some r := rowsOf x | throw "pStep: not in the normalizer"
      let some k' := acts.findIdx? (· == r) | throw "pStep: new action"
      let some v := code.get? (mul x (inv ts[k']!)) | throw "pStep: not in E t_k'"
      eqs := eqs.push (natsV [2 * (12 + k), 2 * (9 + j), 8 * v + 1, 2 * (12 + k')])
  let gs := #[L[6]!, L[7]!, L[8]!, q6, q7]
  let mut nr : Array Val := #[]
  for g in gs do
    let some r := rowsOf g | throw "pStep: not in the normalizer"
    nr := nr.push (natsV r)
  let T := L.extract 0 9 ++ #[q6, q7, one ()] ++ ts
  let words := CFSG.HardMathSupport.Dickson.I271.TabCo1.chainDerivs () ++
    CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeE.ext
  return #[(`T, .list (T.map fun X => .nat (CFSG.KS.RawGen.pack 24 X))),
    (`W, natsV recs.toList),
    (`Q, .list eqs),
    (`NR, .list nr),
    (`TR, .list (acts.map natsV)),
    (`KW, .list (words.toArray.map fun w => natsV (w.map encL)))]

end CertificateChecks.KernelCo1ThreeK.Gen
