module

public import Certificates.Data.Kernel.SporSch.RootPairZ
public meta import Certificates.Kernel.AE6Q8.Chain
public meta import Certificates.Kernel.AE6Q8.Words
public meta import Certificates.Kernel.AE6Core.Chain
public meta import Certificates.Kernel.SporSch.GenRootPairZ
public meta import Certificates.Data.AE6ModelSmall
public import Certificates.Kernel.SporSch.GenRootPairZ
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

namespace CertificateChecks.KernelAE6Sm

meta def xWords : List (List Int) :=
  (Certificates.AE6Model.cutWord :: Certificates.AE6Model.conjWords).map
    (List.map fun (i : Nat) => (Int.ofNat i) + 1)

end CertificateChecks.KernelAE6Sm

#kss_rootpairz CertificateChecks.KernelAE6Sm.ZR 360 9 CertificateChecks.KernelAE6Q8.strongS
  CertificateChecks.KernelAE6Q8.baseS CertificateChecks.KernelAE6Q8.zArr
  CertificateChecks.KernelAE6Q8.rootArrs CertificateChecks.KernelAE6Sm.xWords
  CertificateChecks.KernelAE6Core.gensPL

end
