
module

public import CFSG.Sporadic.Ly.SimpleBase
public import CFSG.Sporadic.Schreier.LyData

@[expose] public section

namespace CFSG.Sporadic.Ly

open CFSG.Sporadic.LySchreier CFSG.Sporadic.Ly.Omega MulAction

theorem b_pow_five [LySeed] : b ^ 5 = 1 := by
  apply mat_injective
  change mat (b ^ 5) = mat 1
  rw [mat_one]
  change ((b ^ 5 : J) : GL (Fin 111) (ZMod 5)).val = 1
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]
  exact mB_pow

theorem mat_npow [LySeed] (g : J) : ∀ n : ℕ, mat (g ^ n) = mat g ^ n
  | 0 => by rw [pow_zero, pow_zero, mat_one]
  | n + 1 => by rw [pow_succ, pow_succ, mat_mul, mat_npow g n]

noncomputable abbrev gConj [LySeed] : J := (a * b ^ 4) ^ 2

theorem card_closure_le [LySeed] {x : J} {n : ℕ} (hn : 0 < n) (hx : x ^ n = 1) :
    Nat.card (Subgroup.closure ({1, x} : Set J)) ≤ n := by
  have e : Subgroup.closure ({1, x} : Set J) = Subgroup.zpowers x := by
    refine le_antisymm ?_ ?_
    · rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers _
    · rw [Subgroup.zpowers_le]
      exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  rw [e, Nat.card_zpowers]
  exact Nat.le_of_dvd hn (orderOf_dvd_of_pow_eq_one hx)

theorem mat_conj [LySeed] : mat (a * (gConj⁻¹ * b * gConj)) = mX := by
  have hb : (b ^ 4)⁻¹ = b := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ]
    exact b_pow_five
  have hi : gConj⁻¹ = (b * a) * (b * a) := by
    rw [gConj, pow_two, _root_.mul_inv_rev, _root_.mul_inv_rev, hb, a_inv]
  rw [hi, gConj, pow_two]
  simp only [mat_mul, mat_npow, mat_a, mat_b]
  simp only [Matrix.mul_assoc]

end CFSG.Sporadic.Ly
