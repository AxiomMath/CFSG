module

public import CFSG.Permutation.FinPack
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fintype.Perm

public section

namespace CFSG.Permutation.FinPack

open Equiv Finset

variable {n : ℕ}

@[expose] def vbit (v : Fin n → ZMod 2) (i : ℕ) : ℕ := if h : i < n then (v ⟨i, h⟩).val else 0

@[expose] noncomputable def vcode (v : Fin n → ZMod 2) : ℕ := encF (vbit v) n

theorem vbit_lt (v : Fin n → ZMod 2) (i : ℕ) : vbit v i < 16 := by
  unfold vbit
  split
  · exact lt_of_lt_of_le (ZMod.val_lt _) (by norm_num)
  · norm_num

theorem rd_vcode (v : Fin n → ZMod 2) (i : Fin n) : rd (vcode v) i = (v i).val := by
  rw [vcode, rd_encF (fun j _ => vbit_lt v j) i.isLt, vbit, dif_pos i.isLt]

theorem vcode_inj {u w : Fin n → ZMod 2} (h : vcode u = vcode w) : u = w :=
  funext fun i => ZMod.val_injective _ (by rw [← rd_vcode u i, ← rd_vcode w i, h])

theorem vcode_eq_iff {u w : Fin n → ZMod 2} : u = w ↔ vcode u = vcode w :=
  ⟨congrArg vcode, vcode_inj⟩

theorem beq_vcode_iff {u w : Fin n → ZMod 2} : Nat.beq (vcode u) (vcode w) = true ↔ u = w := by
  rw [Nat.beq_eq, vcode_eq_iff]

theorem vcode_comp (hn : n ≤ 16) (v : Fin n → ZMod 2) (τ : Perm (Fin n)) :
    vcode (fun i => v (τ i)) = mulK n (vcode v) (enc τ) := by
  rw [mulK, vcode]
  refine encF_congr fun i hi => ?_
  have h1 : rd (enc τ) i = τ ⟨i, hi⟩ := rd_enc hn τ ⟨i, hi⟩
  rw [vbit, dif_pos hi, h1, rd_vcode]

theorem vcode_inv_apply (hn : n ≤ 16) (v : Fin n → ZMod 2) (τ : Perm (Fin n)) :
    vcode (fun i => v (τ⁻¹⁻¹ i)) = mulK n (vcode v) (enc τ) := by
  simp only [inv_inv]
  exact vcode_comp hn v τ

theorem card_filter_inv (P : Perm (Fin n) → Prop) [DecidablePred P] :
    (univ.filter P).card = (univ.filter fun τ => P τ⁻¹).card := by
  refine Finset.card_nbij' (· ⁻¹) (· ⁻¹) ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hσ ⊢
    rwa [inv_inv]
  · intro τ hτ
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hτ ⊢
    exact hτ
  · intro σ _
    exact inv_inv σ
  · intro τ _
    exact inv_inv τ

end CFSG.Permutation.FinPack
