module

public import Mathlib.GroupTheory.Perm.Support
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

open Equiv

namespace Certificates

open Equiv in
theorem certificate4 :
      ∀ t s : Equiv.Perm (Fin 4), t.support.card = 4 → t ^ 2 ≠ 1 →
        s.support.card = 4 → s ^ 2 ≠ 1 →
          ∃ g : Equiv.Perm (Fin 4), g * t * g⁻¹ = s := by
  intro t s ht ht2 hs hs2
  revert t s ht ht2 hs hs2
  decide +kernel

end Certificates
