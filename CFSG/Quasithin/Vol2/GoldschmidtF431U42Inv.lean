module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Pair4

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin CFSG.Open U42F431
open scoped Pointwise

@[expose] def t45 : P45 := mkPerm t0L t0L (by decide +kernel)

theorem repL_t45 : RepL t0L t45 := repL_mkPerm _ _ _ (by decide +kernel)

theorem evalW_t0W : evalW t0W = t0L := by decide +kernel

theorem wordP_t0W : wordP t0W = t45 :=
  eq_of_repL (l := t0L) (evalW_t0W ▸ repL_wordP t0W) repL_t45

@[expose] def tY : Y := ⟨t45, by rw [← wordP_t0W]; exact wordP_mem _⟩

theorem tY_mem_T : tY ∈ T := by
  have hi : t0Idx < 64 := by decide
  obtain ⟨g, hg, hrep⟩ := exists_Tel hi
  have : g = tY := Subtype.ext (eq_of_repL hrep repL_t45)
  rwa [← this]

theorem t45_sq : t45 * t45 = 1 := by
  refine eq_of_repL (l := comp t0L t0L) (repL_mul repL_t45 repL_t45) ?_
  have : comp t0L t0L = idL := by decide +kernel
  rw [this]
  exact repL_one 45

theorem tY_ne_one : tY ≠ 1 := by
  intro h
  have h1 : t45 = 1 := congrArg Subtype.val h
  have : t0L = idL := repL_unique repL_t45 (by rw [h1]; exact repL_one 45)
  revert this
  decide +kernel

theorem orderOf_xY : orderOf xY = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact xY_sq) xY_ne_one

theorem orderOf_tY : orderOf tY = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact Subtype.ext t45_sq) tY_ne_one

theorem card_fix_x : (Finset.univ.filter fun p : Fin 45 => x45 p = p).card = 13 := by
  decide +kernel

theorem card_fix_t : (Finset.univ.filter fun p : Fin 45 => t45 p = p).card = 5 := by
  decide +kernel

end CFSG.Quasithin.H13.F431.U42
