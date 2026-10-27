module

public import Mathlib.Algebra.Polynomial.Roots

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

theorem exists_units_zpow_ne_one {L : Type*} [Field L] [Infinite L] {m : ℤ} (hm : m ≠ 0) :
    ∃ ζ : Lˣ, ζ ^ m ≠ 1 := by
  classical
  have hm' : 0 < m.natAbs := Int.natAbs_pos.2 hm
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset
    ((Polynomial.nthRoots m.natAbs (1 : L)).toFinset ∪ {0})
  simp only [Finset.mem_union, Multiset.mem_toFinset, Polynomial.mem_nthRoots hm',
    Finset.mem_singleton, not_or] at hc
  refine ⟨Units.mk0 c hc.2, fun h => hc.1 ?_⟩
  have h' : (Units.mk0 c hc.2) ^ (m.natAbs : ℤ) = 1 := by
    rcases Int.natAbs_eq m with he | he
    · rw [← he]
      exact h
    · rw [← neg_neg (m.natAbs : ℤ), ← he, zpow_neg, h, inv_one]
  have h'' := congrArg Units.val h'
  rw [zpow_natCast, Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one] at h''
  exact h''

end CFSG.HardMathSupport.Timmesfeld.LangTorus
