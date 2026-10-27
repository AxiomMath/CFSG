module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
meta import CFSG.Milestones.ASVolI.F48.D43.Inputs
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
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.Load

set_option maxRecDepth 400000

namespace CertificateChecks.KernelD43

open CFSG.ASVolI

meta def trGens : Array (Array Nat) := (Array.range 8).map fun k => burnsideF48d_gen k

meta def trInv (t : Array Nat) : Array Nat := Id.run do
  let mut r := Array.replicate 26572 0
  for i in [0:26572] do
    r := r.set! t[i]! i
  return r

meta def trEnc (w : List (Fin 8 × Bool)) : Nat :=
  w.foldl (fun acc l => acc * 32 + (if l.2 then l.1.val + 1 else l.1.val + 9)) 0

meta def trWords : Array Nat := burnsideF48d_LW.toArray.map trEnc

meta def trLen (w : Nat) : Nat := Id.run do
  let mut w := w
  let mut c := 0
  for _ in [0:64] do
    if w > 0 then
      w := w / 32
      c := c + 1
  return c

meta def trLetters : Array (Array Nat) :=
  let G := trGens
  let Gi := G.map trInv
  trWords.map fun w0 => (Array.range 26572).map fun p0 => Id.run do
    let mut w := w0
    let mut p := p0
    for _ in [0:24] do
      let d := w % 32
      if 1 ≤ d && d ≤ 8 then p := (G[d - 1]!)[p]!
      if 9 ≤ d && d ≤ 16 then p := (Gi[d - 9]!)[p]!
      w := w / 32
    return p

meta def trLevels : Array (Array Nat × Nat × Nat) :=
  ((Array.range 8).map fun i => (#[0, 26571, 6, 479, 15916, 186, 1, 3], i, 0)) ++
    ((Array.range 5).map fun i => (#[6, 26571, 15916, 1, 3], i, 2))

meta def trLvLetters (L : Array (Array Nat)) (b : Array Nat) (i lo : Nat) : Array Nat :=
  let lens := trWords.map trLen
  ((Array.range 17).filter fun j =>
    lo ≤ j && (List.range i).all fun u => (L[j]!)[b[u]!]! == b[u]!).qsort
      fun a c => lens[a]! < lens[c]! || (lens[a]! == lens[c]! && a < c)

meta def trBfs (L : Array (Array Nat)) (S : Array Nat) (r : Nat) : Array Nat := Id.run do
  let mut seen := (Array.replicate 26572 false).set! r true
  let mut pts : Array Nat := #[r]
  let mut recs : Array Nat := #[r]
  for h in [0:26572] do
    if h < pts.size then
      let p := pts[h]!
      for j in S do
        let q := (L[j]!)[p]!
        if !seen[q]! then
          seen := seen.set! q true
          recs := recs.push (q ||| (h <<< 15) ||| (j <<< 30))
          pts := pts.push q
  return recs

meta def trAll : Array (Array Nat) :=
  let L := trLetters
  trLevels.map fun x => trBfs L (trLvLetters L x.1 x.2.1 x.2.2) x.1[x.2.1]!

meta def trRows (k : Nat) (a : Array Nat) : Array (Array Nat) :=
  (Array.range ((a.size + k - 1) / k)).map fun r =>
    ((Array.range k).filter fun i => k * r + i < a.size).map fun i => a[k * r + i]!

meta def trWordSrc : Array (Array Nat) := trWords.map fun w => #[w]

meta def trRecSrc : Array (Array Nat) := trRows 16 (trAll.foldl (· ++ ·) #[])

meta def trPosSrc : Array (Array Nat) := Id.run do
  let A := trAll
  let mut pos := Array.replicate (26572 * A.size) 0
  for l in [0:A.size] do
    let R := A[l]!
    for t in [0:R.size] do
      pos := pos.set! (26572 * l + R[t]! % 32768) t
  return trRows 64 pos

end CertificateChecks.KernelD43

#kc_items CertificateChecks.KernelD43.TW include_bytes "data/TreeData.TW.items" 172 3019100911058284743
#kc_items CertificateChecks.KernelD43.TR include_bytes "data/TreeData.TR.items" 251359 11310491548943335884
#kc_items CertificateChecks.KernelD43.TQ include_bytes "data/TreeData.TQ.items" 171126 3787318443991733642
