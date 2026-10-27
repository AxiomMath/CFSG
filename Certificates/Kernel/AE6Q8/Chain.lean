module

public import CFSG.Certificates.Kernel.Spor.RawSound
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Certificates.Kernel.SporSch.Mathieu.Gen
public meta import Certificates.Data.AE6ModelSmall
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.SporSch.Mathieu.Gen
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

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelAE6Q8

open CFSG.KS.SporSch.MOCG

meta def strongS : Array (Array Nat) :=
  strongOf 360 ((Certificates.AE6Model.sLetters.map fun i =>
    CFSG.EvenSmallLie.OmegaEight.genArrs[i]!).toArray) Certificates.AE6Model.sDerive

meta def baseS : Array Nat := #[0, 2, 4, 24, 8]

meta def zArr : Array Nat :=
  Certificates.AE6Model.zWord.foldr (fun i acc =>
    comp (CFSG.EvenSmallLie.OmegaEight.genArrs[i]!) acc) (idA 360)

@[expose] def sDeriveK : List (List Int) := [[-2, 3, 2], [-5, 4, 5], [-4, -2, 4, 2]]

end CertificateChecks.KernelAE6Q8

#ks_rawchain CertificateChecks.KernelAE6Q8.SC 360 9 24 CertificateChecks.KernelAE6Q8.strongS
  CertificateChecks.KernelAE6Q8.baseS 4 CertificateChecks.KernelAE6Q8.sDeriveK

end
