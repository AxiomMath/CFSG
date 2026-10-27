module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public meta import CFSG.Certificates.Kernel.Common.Eval
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

set_option maxRecDepth 400000

namespace CertificateChecks.KernelD43

open CFSG.ASVolI CFSG.Sporadic.Fi23.Native

meta def pkW (a : W) : Nat :=
  (a.p0.toNat ||| a.p1.toNat <<< 64) ||| ((a.m0.toNat ||| a.m1.toNat <<< 64) <<< 256)

meta def negN (a : Nat) : Nat := (a >>> 256) ||| ((a % 2 ^ 256) <<< 256)

meta def keysN : Array Nat :=
  let ks := burnsideF48d_keys ()
  (Array.range 26572).map fun p => pkW ks[2 * p]!

meta def keySrc : Array (Array Nat) :=
  let ks := keysN
  (Array.range 1661).map fun j =>
    ((Array.range 16).filter fun i => 16 * j + i < 26572).map fun i => ks[16 * j + i]!

meta def colSrc : List (List Nat) :=
  let T := burnsideF48d_colTab ()
  (List.range 9).map fun k =>
    let R := burnsideF48d_rows T k
    (List.range 84).map fun q => pkW R[q]!

open CFSG.KC.Eval in
meta def colStep : Step := fun _ =>
  return #[(.anonymous,
    Val.list (colSrc.toArray.map fun r => Val.list (r.toArray.map fun x => Val.nat x)))]

meta def canonSrc : Array Nat := keysN.map fun a => min a (negN a)

meta def zeroSrc : Array Nat := Array.replicate 26572 0

end CertificateChecks.KernelD43

#kmisc_packarrs CertificateChecks.KernelD43.KT CertificateChecks.KernelD43.keySrc 512
#kc_eval CertificateChecks.KernelD43 RL CertificateChecks.KernelD43.colStep
#kmisc_sortpair CertificateChecks.KernelD43.OT CertificateChecks.KernelD43.canonSrc
  CertificateChecks.KernelD43.zeroSrc 1 26572
