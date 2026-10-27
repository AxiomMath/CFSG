module

public import Certificates.Kernel.D43.TreeData
meta import CFSG.Milestones.ASVolI.F48.D43.Inputs2
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

open CFSG.ASVolI

meta def r3Gens : Array (Array Nat) := (Array.range 8).map fun k => burnsideF48d_gen k

meta def r3Inv (t : Array Nat) : Array Nat := Id.run do
  let mut r := Array.replicate 26572 0
  for i in [0:26572] do
    r := r.set! t[i]! i
  return r

meta def r3Letters : Array (Array Nat) :=
  let G := r3Gens
  let Gi := G.map r3Inv
  burnsideF48d_LW.toArray.map fun w => (Array.range 26572).map fun p0 =>
    w.foldr (fun l p => if l.2 then (G[l.1.val]!)[p]! else (Gi[l.1.val]!)[p]!) p0

meta def r3Tabs : Array (Array Nat) :=
  r3Letters.foldl (fun acc t => (acc.push t).push (r3Inv t)) #[]

meta def r3Enc (w : List (Fin 17 × Bool)) : Nat :=
  w.foldl (fun acc l => acc * 64 + (2 * l.1.val + (if l.2 then 1 else 2))) 0

meta def r3Ev (T : Array (Array Nat)) (w : List (Fin 17 × Bool)) (p : Nat) : Nat :=
  w.foldr (fun l q => (T[2 * l.1.val + (if l.2 then 0 else 1)]!)[q]!) p

meta def r3Base : List Nat := [0, 26571, 6, 479, 15916, 186, 1, 3]

meta def r3Key (T : Array (Array Nat)) (w : List (Fin 17 × Bool)) : Nat :=
  (List.range 8).foldl (fun acc u => acc ||| (r3Ev T w (r3Base.getD u 0) <<< (16 * u))) 0

meta def r3Rels : List (List (Fin 17 × Bool)) :=
  burnsideF48d_R1 ++ burnsideF48d_R2 ++
    [(List.replicate 6 burnsideF48d_xyW).flatten, burnsideF48d_W1, burnsideF48d_W2]

meta def r3RelSrc : Array (Array Nat) := (r3Rels.map fun w => #[r3Enc w]).toArray

meta def r3KWSrc : Array (Array Nat) := (burnsideF48d_KW.map fun w => #[r3Enc w]).toArray

meta def r3KKSrc : Array (Array Nat) :=
  let T := r3Tabs
  (burnsideF48d_KW.map fun w => #[r3Key T w]).toArray

meta def r3XSrc : Array (Array Nat) :=
  (burnsideF48d_KW.tail.map fun c => #[r3Enc (burnsideF48d_xyW ++ c)]).toArray

meta def r3YSrc : Array (Array Nat) :=
  (burnsideF48d_KW.tail.map fun c => #[r3Enc (c ++ burnsideF48d_xyW)]).toArray

end CertificateChecks.KernelD43

#kmisc_packarrs CertificateChecks.KernelD43.R3W CertificateChecks.KernelD43.r3RelSrc 240
#kmisc_packarrs CertificateChecks.KernelD43.K3W CertificateChecks.KernelD43.r3KWSrc 240
#kmisc_packarrs CertificateChecks.KernelD43.K3K CertificateChecks.KernelD43.r3KKSrc 128
#kmisc_packarrs CertificateChecks.KernelD43.X3W CertificateChecks.KernelD43.r3XSrc 240
#kmisc_packarrs CertificateChecks.KernelD43.Y3W CertificateChecks.KernelD43.r3YSrc 240
