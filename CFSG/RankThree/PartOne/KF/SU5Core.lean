module

public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.RankThree.PartOne.KF.SU5Centralizer
public import CFSG.RankThree.PartOne.KF.SU5Fixed
public import CFSG.RankThree.PartOne.KF.SU5Swap

public section

namespace CFSG.RankThree.PartOne.KFSU5

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

variable {f : ℕ} {K : Type} [Field K]

theorem odd_card_sub_one (h : UnitaryFieldData 2 f K) : Odd (Nat.card K - 1) := by
  have hf := h.one_le
  have h1 : Even (Nat.card K) := by
    rw [h.card]
    exact (Nat.even_pow.mpr ⟨even_two, by omega⟩)
  have h2 : 1 ≤ Nat.card K := by
    rw [h.card]; exact Nat.one_le_pow _ _ (by norm_num)
  exact Nat.Even.sub_odd h2 h1 odd_one

theorem exists_involution_commuting (h : UnitaryFieldData 2 f K) (Ã S : Subgroup (GL (Fin 5) K))
    (hdiag : ∀ a ∈ Ã, ((a : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).IsDiag)
    (hSle : S ≤ unitarySU 2 f K 5) (hS2 : IsPGroup 2 S) (hSne : S ≠ ⊥)
    (hnorm : ∀ a ∈ Ã, ∀ s ∈ S, a * s * a⁻¹ ∈ S) :
    ∃ t ∈ unitarySU 2 f K 5, orderOf t = 2 ∧ ∀ a ∈ Ã, t * a = a * t := by
  classical
  have : Finite K := h.finite
  have : CharP K 2 := h.charP
  have hK2 : 2 ∣ Nat.card K := by
    rw [h.card]
    exact dvd_pow_self 2 (by have := h.one_le; omega)
  have hunit : ∀ s ∈ S, (((s : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).map h.bar)ᵀ *
      ((s : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) = 1 :=
    fun s hs => ((mem_unitarySU_iff h).mp (hSle hs)).2
  have hcoin : ∃ i j : Fin 5, i ≠ j ∧
      ∀ a ∈ Ã, ((a : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) i i =
        ((a : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) j j := by
    by_contra hcon
    push Not at hcon
    exact hSne (eq_bot_of_normalized_two_group hK2 h.bar Ã S hdiag hcon hunit hS2 hnorm)
  obtain ⟨i, j, hij, hcoin⟩ := hcoin
  refine ⟨swapUnit K i j, ?_, orderOf_swapUnit hij, fun a ha =>
    swapUnit_mul_comm a (hdiag a ha) (hcoin a ha)⟩
  rw [mem_unitarySU_iff h, swapUnit_val, det_swapMatrix, swapMatrix_map, swapMatrix_transpose,
    swapMatrix_mul_self]
  exact ⟨rfl, rfl⟩

theorem eq_one_of_mem_closure_twoElements_su5 (h : UnitaryFieldData 2 f K)
    (Ã : Subgroup (GL (Fin 5) K))
    (hdiag : ∀ a ∈ Ã, ((a : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).IsDiag)
    (hexp : ∀ a ∈ Ã, a ^ 5 = 1) (hcard : 5 < Nat.card Ã) {x : GL (Fin 5) K}
    (hx : x ∈ Subgroup.closure {y : GL (Fin 5) K |
      y ∈ Subgroup.centralizer (Ã : Set (GL (Fin 5) K)) ∧ ∃ k : ℕ, orderOf y = 2 ^ k})
    (hxA : x ∈ Ã) : x = 1 := by
  have : Finite K := h.finite
  exact eq_one_of_mem_closure_twoElements (odd_card_sub_one h) Nat.prime_five le_rfl Ã hdiag
    hexp (exists_entry_ne_of_card_gt (by norm_num) (by norm_num) Ã hdiag hexp hcard) hx hxA

end CFSG.RankThree.PartOne.KFSU5
