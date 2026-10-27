module

public import Certificates.Data.A5
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

open CFSG.GorensteinWalter
open scoped Matrix MatrixGroups
open Equiv.Perm

namespace Certificates

open CFSG.GorensteinWalter in
open scoped Matrix MatrixGroups in
open Equiv.Perm in
theorem certificate12 : ∀ x : alternatingGroup (Fin 5), x ≠ 1 →
      repPerm x.1 ≠ 1 ∧ repPerm x.1 ≠ -1 := by
  decide

end Certificates
