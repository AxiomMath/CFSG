module

import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Tactic.Bound.Init
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset

public noncomputable section

namespace CFSG.MonoidAlgebra

open _root_.MonoidAlgebra

section Infinite

variable {k : Type*} [Field k] [Infinite k]

theorem exists_zpow_ne_one_of_infinite {z : ℤ} (hz : z ≠ 0) : ∃ t : kˣ, t ^ z ≠ 1 := by
  classical
  have hN : 0 < z.natAbs := Int.natAbs_pos.mpr hz
  have hP : (Polynomial.X ^ z.natAbs - Polynomial.C (1 : k)) ≠ 0 :=
    Polynomial.X_pow_sub_C_ne_zero hN 1
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset
    (insert 0 (Polynomial.X ^ z.natAbs - Polynomial.C (1 : k)).roots.toFinset)
  rw [Finset.mem_insert, not_or, Multiset.mem_toFinset, Polynomial.mem_roots hP,
    Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C, sub_eq_zero] at hx
  obtain ⟨hx0, hx1⟩ := hx
  refine ⟨Units.mk0 x hx0, fun h => hx1 ?_⟩
  have hpow : (Units.mk0 x hx0) ^ (z.natAbs : ℤ) = 1 := by
    rcases Int.natAbs_eq z with hzN | hzN
    · rw [← hzN]
      exact h
    · have h' : (Units.mk0 x hx0) ^ (-(z.natAbs : ℤ)) = 1 := by
        rw [← hzN]
        exact h
      rwa [zpow_neg, inv_eq_one] at h'
  rw [zpow_natCast] at hpow
  have := congrArg Units.val hpow
  rwa [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one] at this

end Infinite

end CFSG.MonoidAlgebra
