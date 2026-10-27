module

public import CFSG.Quasithin.Vol2.Ch6H11Main

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatOm4mA.OuterComm
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatOm4mA.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NatOm4mA

open CFSG.Quasithin
open CFSG.Quasithin.H13
open CFSG.Quasithin.H13.H11M (VH LH UH NH SigInv)

variable {F : Type} [Field F] [CharP F 2] {a : ℕ} (hσ : SigInv a F)

theorem exists_witness_outer [Fintype F] (ha : 1 ≤ a) (hF : Fintype.card F = 2 ^ (2 * a))
    {A : Subgroup (MulAut (VH a F))} (hAN : A ≤ NH hσ) (hA : IsElemAbelian2 A)
    (hstd : A ⊓ LH hσ ≤ UH hσ) (hAL : ¬ A ≤ LH hσ) :
    ∃ B : Subgroup (MulAut (VH a F)), B ≤ A ∧ E3.mQuot A B ≤ a ∧ fixV B ≠ fixV A := by
  obtain ⟨f, hfA, hfL⟩ := Set.not_subset.mp hAL
  obtain ⟨θ₀, hθ₀⟩ := H11M.exists_sig_ne ha hF
  have hsq : ∀ x ∈ A, x * x = 1 := fun x hx => by rw [← sq]; exact hA.2 x hx
  obtain ⟨M, hM⟩ := (H11M.mem_LH_or_formS hσ ha hF hθ₀ (hAN hfA) (hsq f hfA)).resolve_left hfL
  have hf1 : f ≠ 1 := fun h => hfL (by rw [h]; exact Subgroup.one_mem _)
  have hf2 : orderOf f = 2 := orderOf_eq_prime (hA.2 f hfA) hf1
  have hA1 : A ≠ ⊥ := fun h => hf1 (by simpa [h] using hfA)
  have hcard := card_eq_two_mul_inf_LH hσ ha hF hθ₀ hAN hA hfA hfL
  have hle := card_inf_LH_le hσ ha hF hA.1 hstd hfA hM
  by_cases h0 : A ⊓ LH hσ = ⊥
  · have hA2 : Nat.card A = 2 := by rw [hcard, h0, Subgroup.card_bot, mul_one]
    have hAle : Nat.card A ≤ 2 ^ a := by
      rw [hA2]
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ a := pow_le_pow_right' (by norm_num) ha
    exact ⟨⊥, bot_le, mQuot_bot_le_of_card_le A hAle, fixV_bot_ne_of_ne_bot hA1⟩
  · have hk : Nat.card A ≤ 2 ^ (a + 1) := by
      rw [hcard, pow_succ]
      calc 2 * Nat.card ↥(A ⊓ LH hσ) ≤ 2 * 2 ^ a := Nat.mul_le_mul_left 2 hle
        _ = 2 ^ a * 2 := by rw [mul_comm]
    refine ⟨Subgroup.zpowers f, Subgroup.zpowers_le.mpr hfA,
      mQuot_zpowers_le_of_card_le hfA hf2 hk, ?_⟩
    have hft : Nat.card (fixV (Subgroup.zpowers f)) = (2 ^ a) ^ 3 :=
      H11M.card_fix_formS hσ ha hF hθ₀ hM
    have hCle : Nat.card (fixV A) ≤ Nat.card (fixV (A ⊓ LH hσ)) :=
      Subgroup.card_le_of_le (H11M.fixV_anti inf_le_left)
    have hbound : Nat.card ↥(A ⊓ LH hσ) * Nat.card (fixV (A ⊓ LH hσ)) * 2 ^ a ≤
        (2 ^ a) ^ 4 := (H11M.card_fix_le_of_uuH hσ ha hF hstd h0).1
    have h2c : 2 ≤ Nat.card ↥(A ⊓ LH hσ) :=
      Nat.succ_le_of_lt ((Subgroup.one_lt_card_iff_ne_bot (A ⊓ LH hσ)).mpr h0)
    have hq : 0 < 2 ^ a := Nat.two_pow_pos a
    have h1 : 2 * Nat.card (fixV (A ⊓ LH hσ)) * 2 ^ a ≤ (2 ^ a) ^ 3 * 2 ^ a := by
      calc 2 * Nat.card (fixV (A ⊓ LH hσ)) * 2 ^ a
          ≤ Nat.card ↥(A ⊓ LH hσ) * Nat.card (fixV (A ⊓ LH hσ)) * 2 ^ a :=
            Nat.mul_le_mul_right (2 ^ a) (Nat.mul_le_mul_right _ h2c)
        _ ≤ (2 ^ a) ^ 4 := hbound
        _ = (2 ^ a) ^ 3 * 2 ^ a := by ring
    have h2 : 2 * Nat.card (fixV (A ⊓ LH hσ)) ≤ (2 ^ a) ^ 3 :=
      Nat.le_of_mul_le_mul_right h1 hq
    have hd : 0 < Nat.card (fixV (A ⊓ LH hσ)) := by
      haveI : Nonempty ↥(fixV (A ⊓ LH hσ)) := ⟨1, Subgroup.one_mem _⟩
      exact Nat.card_pos
    have hlt : Nat.card (fixV (A ⊓ LH hσ)) < (2 ^ a) ^ 3 := by omega
    have hltA : Nat.card (fixV A) < (2 ^ a) ^ 3 := lt_of_le_of_lt hCle hlt
    exact fun heq => absurd (by rw [← heq, hft] at hltA; exact hltA) (lt_irrefl _)

end CFSG.LocalAnalysis.UniquenessCase.UC22.NatOm4mA
