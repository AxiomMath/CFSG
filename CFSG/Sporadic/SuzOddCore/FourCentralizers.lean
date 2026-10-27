module

public import CFSG.Sporadic.SuzOddCore.InvCentralizers

public noncomputable section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Certificates

theorem suzInv_mem_iff_inM
    {i : ℕ} (hi : i < 4) : suzInv i ∈ suzM ↔ inM (tArr i) = true :=
  (inM_iff (rep_suzInv hi)).symm

theorem CTUC_Suz_four_exact_involution_centralizers :
    (∀ i < 4, orderOf (suzInv i) = 2) ∧
    (Finset.univ.filter fun x : Fin 1782 => suzInv 0 x = x).card = 42 ∧
    (Finset.univ.filter fun x : Fin 1782 => suzInv 1 x = x).card = 54 ∧
    (Finset.univ.filter fun x : Fin 1782 => suzInv 2 x = x).card = 0 ∧
    (Finset.univ.filter fun x : Fin 1782 => suzInv 3 x = x).card = 100 ∧
    suzInv 0 ∈ suzM ∧ suzInv 1 ∈ suzM ∧ suzInv 2 ∉ suzM ∧ suzInv 3 ∉ suzM ∧
    (∀ i < 4, ValidSchreier (invFullChain i) ∧ ValidSchreier (invInnerChain i)) ∧
    (∀ i < 4, invD i = centT (suzInv i) ∧ invE i = centM (suzInv i)) ∧
    Nat.card (invD 0) = 322560 ∧ Nat.card (invD 1) = 6635520 ∧ Nat.card (invD 2) = 380160 ∧
    Nat.card (invD 3) = 2419200 ∧
    Nat.card (invE 0) = 161280 ∧ Nat.card (invE 1) = 3317760 ∧ Nat.card (invE 2) = 190080 ∧
    Nat.card (invE 3) = 1209600 ∧
    (∀ i < 4, invE i ≤ invD i ∧ ((invE i).subgroupOf (invD i)).Normal ∧
      ((invE i).subgroupOf (invD i)).index = 2) := by
  obtain ⟨-, h0, h1, h2, h3, -⟩ := invT_check
  refine ⟨fun i hi => orderOf_suzInv hi, suzInv_fixed (i := 0) (by norm_num),
    suzInv_fixed (i := 1) (by norm_num), suzInv_fixed (i := 2) (by norm_num),
    suzInv_fixed (i := 3) (by norm_num), (suzInv_mem_iff_inM (by norm_num)).2 h0,
    (suzInv_mem_iff_inM (by norm_num)).2 h1, fun h => ?_, fun h => ?_,
    fun i hi => invChains_valid hi, fun i hi => ⟨invD_eq_centT hi, invE_eq_centM hi⟩,
    card_invD (i := 0) (by norm_num), card_invD (i := 1) (by norm_num),
    card_invD (i := 2) (by norm_num), card_invD (i := 3) (by norm_num),
    card_invE (i := 0) (by norm_num), card_invE (i := 1) (by norm_num),
    card_invE (i := 2) (by norm_num), card_invE (i := 3) (by norm_num),
    fun i hi => ⟨invE_le_invD hi, Subgroup.normal_of_index_eq_two (invE_index hi),
      invE_index hi⟩⟩
  · rw [suzInv_mem_iff_inM (by norm_num), h2] at h
    exact Bool.false_ne_true h
  · rw [suzInv_mem_iff_inM (by norm_num), h3] at h
    exact Bool.false_ne_true h

end CFSG.Sporadic.SuzOddCore
