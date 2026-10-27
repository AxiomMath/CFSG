module

public import Mathlib.Algebra.Group.End
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

namespace Certificates

theorem certificate44 : ∀ (a s : Equiv.Perm (Fin 4)),
        (a ≠ 1 ∧ a ^ 3 = 1) → (s ≠ 1 ∧ s ^ 2 = 1) →
        (∀ c : Equiv.Perm (Fin 4), c * s = s * c →
          c * a * c⁻¹ = a ∨ c * a * c⁻¹ = a ^ 2) →
        a * s = s * a := by
  decide +kernel

end Certificates
