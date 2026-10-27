module

public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Data.Kernel.Spor.MulH
meta import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeData
import CFSG.Certificates.Kernel.Common.Harness
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

namespace CertificateChecks.KernelD42Tri

meta def gM : Array (Array Nat) := CFSG.EvenSmallLie.OmegaEight.genArrs.extract 0 8

meta def giM : Array (Array Nat) := gM.map (CFSG.KS.RawGen.inv 360)

meta def rM : Array Nat := CFSG.EvenSmallLie.OmegaEight.rhoArr

end CertificateChecks.KernelD42Tri

#kmulh CertificateChecks.KernelD42Tri.RC 360 9 CertificateChecks.KernelD42Tri.gM
  CertificateChecks.KernelD42Tri.giM CertificateChecks.KernelD42Tri.rM 14400

namespace CertificateChecks.KernelD42Tri

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH

theorem rcCanon : bAnd(allN 8 (fun j => bAnd(canonK 360 9 (mask 9) (360 * 9) (RC.G j),
      canonK 360 9 (mask 9) (360 * 9) (RC.GI j))),
    bAnd(canonK 360 9 (mask 9) (360 * 9) RC.R, szOK 360 9)) = true := by
  quickRfl

theorem rcCnt : Nat.beq RC.cnt 14400 = true := by quickRfl

theorem rcHd : penumHdK RC.R RC.cnt 14400 RC.T RC.PL = true := by quickRfl

end CertificateChecks.KernelD42Tri

end
