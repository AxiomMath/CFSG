module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteGeoChain
public import Mathlib.GroupTheory.Index

public section

namespace CFSG.Quasithin.Fan86.Tutte.Geo

open CFSG.Quasithin.F6.GoldAmL3T CFSG.Quasithin.Fan86.Tutte.Red

variable {W : Type} {Γ : SimpleGraph W} {H : Type} [Group H] [MulAction H W] {s : ℕ}

namespace RegData

variable (R : RegData Γ H s)

include R

theorem relIndex_chain (a : Arc Γ s) {i : ℕ} (hi : i + 1 ≤ s) :
    (chain a H i).relIndex (chain a H (i + 1)) = if i + 1 = s then 3 else 2 := by
  have key := R.orbit_chain a (n := s - (i + 1)) (by omega)
  have e : s - (s - (i + 1)) = i + 1 := by omega
  rw [e] at key
  rw [chain_eq_inf hi, Subgroup.inf_relIndex_left, Subgroup.relIndex]
  have h2 : (MulAction.stabilizer H (a.vert (s - (i + 1) + 1))).subgroupOf (chain a H (i + 1)) =
      MulAction.stabilizer ↥(chain a H (i + 1)) (a.vert (s - (i + 1) + 1)) := by
    ext g
    simp [MulAction.mem_stabilizer_iff]
  rw [h2, MulAction.index_stabilizer, key, extSet_ncard R.card3]
  split_ifs <;> omega

theorem card_chain_lt (a : Arc Γ s) : ∀ i, i < s → Nat.card (chain a H i) = 2 ^ i
  | 0, _ => by rw [chain_zero R a]; simp
  | i + 1, hi => by
    have h1 := Subgroup.relIndex_mul_card (H := chain a H i) (K := chain a H (i + 1))
    have e : (if i + 1 = s then 3 else 2) = 2 := by split_ifs <;> omega
    rw [inf_eq_left.mpr (chain_mono a i), R.relIndex_chain a (by omega), e,
      card_chain_lt a i (by omega)] at h1
    rw [pow_succ]
    omega

theorem card_chain_s (a : Arc Γ s) : Nat.card (chain a H s) = 3 * 2 ^ (s - 1) := by
  have h1 := Subgroup.relIndex_mul_card (H := chain a H (s - 1)) (K := chain a H (s - 1 + 1))
  rw [inf_eq_left.mpr (chain_mono a (s - 1)), R.relIndex_chain a (by have := R.one_le; omega)] at h1
  rw [Nat.sub_add_cancel R.one_le] at h1
  have e : (if s = s then 3 else 2) = 3 := by simp
  rw [e, R.card_chain_lt a (s - 1) (by have := R.one_le; omega)] at h1
  omega

end RegData

end CFSG.Quasithin.Fan86.Tutte.Geo
