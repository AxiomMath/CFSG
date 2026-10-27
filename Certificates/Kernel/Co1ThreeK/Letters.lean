module

public import Certificates.Data.Kernel.SporSch.Co1MatW
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1ThreeData
public meta import Certificates.Kernel.SporSch.Co1.GenDag
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1ThreeInputs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.SporSch.Co1.GenDag
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

namespace CertificateChecks.KernelCo1ThreeK

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T CFSG.Sporadic.Co1Schreier.Native

meta def lettersD : List Rows × List Rows × Bool := (Native.lRows (), Native.lInvs (), true)

meta def rootsD : List Rows × List Rows × Bool :=
  ((List.range 3).map Native.rootRows, (List.range 3).map fun j => inv (Native.rootRows j), true)

end CertificateChecks.KernelCo1ThreeK

#kss_co1dag CertificateChecks.KernelCo1ThreeK.L CertificateChecks.KernelCo1ThreeK.lettersD
#kss_co1dag CertificateChecks.KernelCo1ThreeK.R CertificateChecks.KernelCo1ThreeK.rootsD

namespace CertificateChecks.KernelCo1ThreeK

open CFSG.KC.Enum CFSG.KS.SporSch.M24 CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T

@[expose] noncomputable def SM (i : Nat) : Nat := L.M (Nat.add (nat_lit 9) i)

@[expose] noncomputable def SMI (i : Nat) : Nat := L.MI (Nat.add (nat_lit 9) i)

theorem kS : dagWK SM SMI 2 66 Data.dagWords = true := by quickRfl

theorem kI : allN 9 (fun k => invOKW (L.M k) (L.MI k)) = true := by quickRfl

theorem kR : allN 3 (fun j => bAnd(lettersK 75 (Data.rootWords.getD j []),
    bAnd(Nat.beq (wordWK L.M L.MI (Data.rootWords.getD j [])) (R.M j),
      invOKW (R.M j) (R.MI j)))) = true := by quickRfl

end CertificateChecks.KernelCo1ThreeK

end
