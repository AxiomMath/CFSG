module

public meta import Lean
public meta import Std.Data.HashSet
public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1ThreeInputs
public import Certificates.Data.CFSGNative.Co1Schreier.Base
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

namespace CertificateChecks.KernelCo1ThreeK.GenLeaf

open CFSG.KC.Eval CFSG.Sporadic.Co1Schreier.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T Timmesfeld.Co1Leaf

meta def natsV (xs : List Nat) : Val := .list (xs.toArray.map .nat)

meta def eFs : List (List Nat) := [[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0], [1, 0, 0, 1, 2, 0]]

meta def maskOf (l : List Nat) : Nat := l.foldl (fun m i => m ^^^ (1 <<< i)) 0

meta def selTests (xs : Std.HashSet Nat) (B : List Nat) (levels : List (List (Nat × Nat))) :
    Except String (List (List Nat) × Nat × Nat × Nat) := do
  let mut P : List (List Nat) := [[]]
  let mut T : Array (List Nat) := #[]
  let mut cand := 0
  let mut nt := 0
  for lev in levels do
    let full := dfsStep xs B P lev
    let mut C := dfsStep xs B P []
    cand := cand + C.length
    let mut sel : Array Nat := #[]
    for t in lev do
      if C.length == full.length then break
      let C' := C.filter (levelOK xs B [t])
      if C'.length < C.length then
        sel := sel.push (t.1 ^^^ xorSel B t.2)
        C := C'
    if C.length != full.length then throw "selTests: the level does not reduce"
    T := T.push sel.toList
    nt := nt + sel.size
    P := full
  return (T.toList, cand, nt, P.length)

public meta def leafStep (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  if args.size != 0 then throw "leafStep: expected no arguments"
  let X := Native.xList ()
  let xs := Std.HashSet.ofList X
  let pk := fun (R : Rows) => Val.nat (CFSG.KS.RawGen.pack 24 R)
  let planes := Native.planeRows () ++ (List.range 4).flatMap Native.childPlane
  let leaves := eFs.map (kerElts 3 (Native.aGens ())) ++ Native.dLeaves ()
  if leaves.length != 19 then throw "leafStep: 19 leaves expected"
  let mut out : Array (Lean.Name × Val) := #[
    (`PD, .list (planes.toArray.map pk)),
    (`EV, .list (eFs.toArray.map fun f => .list ((kerBasis 3 f).toArray.map natsV))),
    (`DV, .list ((normVecs 3 2).toArray.map fun f => natsV ((kerBasis 3 f).headD [])))]
  let mut st : Array Val := #[]
  for (gs, l) in leaves.zipIdx do
    let D := leafData X gs
    let els := eltsOf gs
    let piR := sumIdx els D.piL
    let B := D.basis
    let T := testData X (CFSG.Sporadic.SmallF2.Native.transposeRows 24 piR) B
    let levels := (List.range B.length).map (levelData T)
    let (TS, cand, nt, ns) ← selTests xs B levels
    if !leafOK X xs gs ⟨D.piL, D.w, D.span, B⟩ then throw s!"leafStep: leaf {l} fails"
    out := out ++ #[(Lean.Name.mkSimple s!"P{l}", .nat (maskOf D.piL)),
      (Lean.Name.mkSimple s!"W{l}", .nat D.w),
      (Lean.Name.mkSimple s!"S{l}", natsV (D.span.map maskOf)),
      (Lean.Name.mkSimple s!"B{l}", natsV B),
      (Lean.Name.mkSimple s!"T{l}", .list (TS.toArray.map natsV))]
    st := st.push (natsV [B.length, cand, nt, ns])
  return out.push (`ST, .list st)

end CertificateChecks.KernelCo1ThreeK.GenLeaf
