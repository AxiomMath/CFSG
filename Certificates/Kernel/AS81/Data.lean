module

meta import Certificates.Kernel.SporSch.GenPerms
meta import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3LineTests
import Certificates.Kernel.SporSch.GenPerms
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

namespace CertificateChecks.KernelAS81

open CFSG.ComponentClassification.AS81.MinusLines

meta def cols : Array (Array Nat) :=
  #[lineArr.map (·.1), lineArr.map (·.2.1), lineArr.map (·.2.2)]

meta def plRows : Array (Array Nat) :=
  (Array.range 120).map fun x => pairLine.extract (120 * x) (120 * x + 120)

meta def o1 : Array (Array Nat) := omega1Gens

meta def gens : Array (Array Nat) := lineGens

meta def h0 : Array (Array Nat) := lineH0Arrs

meta def forestData (n : Nat) (G : Array (Array Nat)) (R : Array Nat) : Array (Array Nat) := Id.run do
  let m := R.size
  let mut lab := Array.replicate n m
  let mut dep := Array.replicate n 0
  let mut par := Array.replicate n 0
  let mut gl := Array.replicate n 0
  let mut q : Array Nat := #[]
  for c in [0:m] do
    lab := lab.set! R[c]! c
    q := q.push R[c]!
  let mut cs : Array Nat := #[q.size]
  let mut h := 0
  for _ in [0:n] do
    if h < q.size then
      let x := q[h]!
      h := h + 1
      for i in [0:G.size] do
        let y := (G[i]!)[x]!
        if lab[y]! == m then
          lab := lab.set! y lab[x]!
          dep := dep.set! y (dep[x]! + 1)
          par := par.set! y x
          gl := gl.set! y i
          q := q.push y
      cs := cs.push q.size
  let N := q.size
  let mut pos := Array.replicate n (N + 1)
  for k in [0:N] do
    pos := pos.set! q[k]! k
  return #[R, #[N], q, pos, cs, lab, dep, par, gl]

meta def forT : Array (Array Nat) := forestData 1120 lineGens #[0]

meta def forH : Array (Array Nat) := forestData 1120 lineH0Arrs lineH0Reps

meta def mList (l : Nat) : Array (Nat × Nat × Nat) :=
  (lineMergeSearch 1120 lineGens 0 lineH0Reps[l + 1]!).toArray

meta def mWit (l : Nat) : Array Nat × Array Nat × Array (Array Nat) := Id.run do
  let n := 1120
  let G := lineGens
  let x := lineH0Reps[l + 1]!
  let L := mList l
  let Lc := L.size
  let NS := (Lc + 31) / 32
  let mut lab := Array.ofFn (n := n) fun i => if i.val = x then 0 else i.val
  let mut tp := Array.replicate n Lc
  let mut pp := Array.replicate n 0
  let mut ck : Array (Array Nat) := #[]
  for k in [0:Lc] do
    if k % 32 == 0 then ck := ck.push lab
    let (i, u, v) := L[k]!
    let lp := lab[(G[i]!)[u]!]!
    let lq := lab[(G[i]!)[v]!]!
    if lq != lp then
      tp := tp.set! lq k
      pp := pp.set! lq lp
      lab := lab.map fun z => if z == lq then lp else z
  while ck.size ≤ NS do
    ck := ck.push lab
  return (tp, pp, ck)

meta def mCnt : Array (Array Nat) := (Array.range 4).map fun l => #[(mList l).size]

meta def mRec : Array (Array Nat) := (Array.range 4).map fun l =>
  (mList l).foldl (fun a r => ((a.push r.1).push r.2.1).push r.2.2) #[]

meta def mTime : Array (Array Nat) := (Array.range 4).map fun l => (mWit l).1

meta def mPar : Array (Array Nat) := (Array.range 4).map fun l => (mWit l).2.1

meta def mA0 : Array (Array Nat) := (mWit 0).2.2

meta def mA1 : Array (Array Nat) := (mWit 1).2.2

meta def mA2 : Array (Array Nat) := (mWit 2).2.2

meta def mA3 : Array (Array Nat) := (mWit 3).2.2

end CertificateChecks.KernelAS81

public section

#kss_perms CertificateChecks.KernelAS81.LT 7 CertificateChecks.KernelAS81.cols
#kss_perms CertificateChecks.KernelAS81.PR 11 CertificateChecks.KernelAS81.plRows
#kss_perms CertificateChecks.KernelAS81.O 7 CertificateChecks.KernelAS81.o1
#kss_perms CertificateChecks.KernelAS81.G 11 CertificateChecks.KernelAS81.gens
#kss_perms CertificateChecks.KernelAS81.H 11 CertificateChecks.KernelAS81.h0
#kss_perms CertificateChecks.KernelAS81.FT 11 CertificateChecks.KernelAS81.forT
#kss_perms CertificateChecks.KernelAS81.FH 11 CertificateChecks.KernelAS81.forH
#kss_perms CertificateChecks.KernelAS81.MC 11 CertificateChecks.KernelAS81.mCnt
#kss_perms CertificateChecks.KernelAS81.ML 11 CertificateChecks.KernelAS81.mRec
#kss_perms CertificateChecks.KernelAS81.MT 12 CertificateChecks.KernelAS81.mTime
#kss_perms CertificateChecks.KernelAS81.MP 11 CertificateChecks.KernelAS81.mPar
#kss_perms CertificateChecks.KernelAS81.MA0 11 CertificateChecks.KernelAS81.mA0
#kss_perms CertificateChecks.KernelAS81.MA1 11 CertificateChecks.KernelAS81.mA1
#kss_perms CertificateChecks.KernelAS81.MA2 11 CertificateChecks.KernelAS81.mA2
#kss_perms CertificateChecks.KernelAS81.MA3 11 CertificateChecks.KernelAS81.mA3

end
