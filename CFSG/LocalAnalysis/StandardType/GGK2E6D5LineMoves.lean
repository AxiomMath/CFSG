module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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

public section

namespace CFSG.StandardType

@[expose] def d5SwapVector (i j : Fin 5) (v : Fin 6 → ZMod 3) : Fin 6 → ZMod 3 :=
  v ∘ Equiv.swap i.succ j.succ

@[expose] def d5NegPairVector (i j : Fin 5) (v : Fin 6 → ZMod 3) : Fin 6 → ZMod 3 :=
  fun k => if k = i.succ ∨ k = j.succ then -v k else v k

theorem d5_nonaxis_exists_line_move :
    ∀ v : Fin 6 → ZMod 3, (∃ k : Fin 5, v k.succ ≠ 0) →
      ∃ i j : Fin 5, i ≠ j ∧
        ((∀ c : ZMod 3, d5SwapVector i j v ≠ c • v) ∨
          (∀ c : ZMod 3, d5NegPairVector i j v ≠ c • v)) := by
  decide +kernel

end CFSG.StandardType

end
