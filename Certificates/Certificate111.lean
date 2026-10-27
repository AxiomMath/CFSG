module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenInvariantOddPSubgroupCertificateDefs
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.Measurability.Init
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

public section

open CFSG CFSG.GorensteinWalter

namespace CertificateChecks.Batch111

open CFSG CFSG.GorensteinWalter

private theorem aSeven_order_four_not_centralizes_a7a :
    ∀ x : ASevenCertificateGroup, x ^ 4 = 1 → x ^ 2 ≠ 1 →
      x * a7a ≠ a7a * x := by
  decide +kernel

end CertificateChecks.Batch111

namespace Certificates

open CertificateChecks

open CFSG CFSG.GorensteinWalter in
theorem certificate111 : (∀ x : ASevenCertificateGroup, x ^ 4 = 1 → x ^ 2 ≠ 1 →
      x * a7a ≠ a7a * x) := by
  exact CertificateChecks.Batch111.aSeven_order_four_not_centralizes_a7a

end Certificates
