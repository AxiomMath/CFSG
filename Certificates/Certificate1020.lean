
module


public import Certificates.Data.CFSGNative.Th.Base
import CFSG.Certificates.Kernel.Th.SoundnessTwin
import CFSG.Certificates.Kernel.Th.Checks2.Base_K
import CFSG.Certificates.Kernel.Th.Checks2.Sm_C
import CFSG.Certificates.Kernel.Th.Checks2.Seed_S
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

namespace Certificates

open CFSG CFSG.Sporadic CFSG.Sporadic.Th CFSG.Sporadic.Th.Native Matrix Pointwise in
theorem certificate1020 : (
 formBaseCheck 124 baseCode = true 
)
    ∧ (
 CFSG.Sporadic.Th.Native.eqRows (mulRows (invRows cRows) cRows) idRows = true 
) :=
  CFSG.KC.Th.Soundness.base_sound _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CFSG.KD.ThS.k0
    CFSG.KD.ThSeed.pF CFSG.KC.Th.BaseK.pack_C CFSG.KC.Th.BaseK.gram CFSG.KC.Th.BaseK.inv_C
    CFSG.KC.Th.BaseK.form_base

end Certificates
