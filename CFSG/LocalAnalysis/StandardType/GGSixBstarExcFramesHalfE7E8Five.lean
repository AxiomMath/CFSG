module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfToralDescent
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSylowE8Five

public section

namespace CFSG.StandardType.ExcFramesHalf

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc
open CFSG.Timmesfeld.ExceptionalOrders (geomSum)

local instance excFramesHalfFiveFact : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

theorem card_fix_wordE7Five_four :
    Nat.card {x : Fin Tag.E7.rank → ZMod 5 // torusWord .E7 5 wordE7Five x = x} ≤ 5 ^ (7 - 4) :=
  card_fix_torusWord_le (τ := .E7) wordE7Five ![0, 2, 3, 4] ![0, 1, 2, 3] (by decide)
    ![![1, 2, 2, 2], ![2, 2, 2, 2], ![3, 3, 4, 4], ![0, 0, 0, 1]] (by decide +kernel)

theorem card_fix_wordE8B_four :
    Nat.card {x : Fin Tag.E8.rank → ZMod 5 // torusWord .E8 5 wordE8B x = x} ≤ 5 ^ (8 - 4) :=
  card_fix_torusWord_le (τ := .E8) wordE8B ![0, 5, 6, 7] ![4, 5, 6, 7] (by decide)
    ![![0, 1, 1, 1], ![2, 0, 1, 1], ![1, 0, 0, 1], ![2, 0, 0, 0]] (by decide +kernel)

@[expose] def minorInvE8AB : Fin 5 → Fin 4 → Fin 4 → ZMod 5 :=
  ![![![1, 0, 2, 2], ![0, 2, 0, 0], ![3, 0, 3, 4], ![2, 2, 2, 2]],
    ![![1, 0, 2, 2], ![0, 2, 0, 0], ![3, 0, 3, 4], ![2, 2, 2, 2]],
    ![![1, 0, 2, 2], ![0, 2, 0, 0], ![3, 0, 3, 4], ![2, 2, 2, 2]],
    ![![1, 0, 2, 2], ![0, 2, 0, 0], ![3, 0, 3, 4], ![2, 2, 2, 2]],
    ![![0, 4, 1, 1], ![2, 4, 2, 2], ![2, 4, 2, 3], ![2, 2, 2, 2]]]

theorem minor_wordE8AB_four : ∀ c : Fin 5, ∀ a b : Fin 4,
    ∑ d, minorInvE8AB c a d *
      (torusWord .E8 5 (wordE8AB c) (Pi.single ((![0, 1, 2, 4] : Fin 4 → Fin Tag.E8.rank) b) 1)
        ((![0, 1, 2, 3] : Fin 4 → Fin Tag.E8.rank) d) -
        if (![0, 1, 2, 3] : Fin 4 → Fin Tag.E8.rank) d =
          (![0, 1, 2, 4] : Fin 4 → Fin Tag.E8.rank) b then 1 else 0) =
      if a = b then 1 else 0 := by
  decide +kernel

theorem card_fix_wordE8AB_four {c : ℕ} (hc : c < 5) :
    Nat.card {x : Fin Tag.E8.rank → ZMod 5 // torusWord .E8 5 (wordE8AB c) x = x} ≤
      5 ^ (8 - 4) :=
  card_fix_torusWord_le (τ := .E8) (wordE8AB c) ![0, 1, 2, 3] ![0, 1, 2, 4] (by decide)
    (minorInvE8AB ⟨c, hc⟩) (minor_wordE8AB_four ⟨c, hc⟩)

section Index

variable {K : Type} [Field K]

theorem not_five_dvd_index_weylX_E7 [Finite K] [CharP K 2] (h5 : 5 ∣ Nat.card K - 1) :
    ¬ 5 ∣ (weylX .E7 K (Subgroup.zpowers ((coxeterSystem .E7).wordProd wordE7Five))).index := by
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  have hG := geomSum_five_mod (mod_eq_one_of_dvd_sub_one (by norm_num) hq h5)
  have hq1 : (Nat.card K : ZMod 5) = 1 := cast_eq_one_of_dvd_sub_one hq h5
  have hm1 := cast_div_eq (p := 5) (c := 1) (by norm_num) (by norm_num) hG
  have hGm : geomSum 5 1 (Nat.card K) = 5 * (geomSum 5 1 (Nat.card K) / 5) := by omega
  have hS : Nat.card (Subgroup.zpowers ((coxeterSystem .E7).wordProd wordE7Five)) = 5 := by
    rw [Nat.card_zpowers, orderOf_wordE7Five]
  rw [index_weylX_eq (M := Nat.card K ^ 63 * (geomSum 2 1 (Nat.card K) * geomSum 3 1 (Nat.card K) *
      geomSum 4 1 (Nat.card K) * (geomSum 5 1 (Nat.card K) / 5) *
      (geomSum 2 3 (Nat.card K) * geomSum 8 1 (Nat.card K)) *
      (geomSum 9 1 (Nat.card K) * geomSum 3 4 (Nat.card K)) *
      (geomSum 2 5 (Nat.card K) * geomSum 2 9 (Nat.card K) * geomSum 14 1 (Nat.card K))))
    (by rw [hS, card_adjointGroup_E7_eq, prodE7]; nth_rewrite 1 [hGm]; ring)]
  apply not_dvd_of_cast_ne_zero
  push_cast
  simp only [hq1, hm1, geomSum_cast hq1, one_pow, Nat.cast_one]
  decide

theorem not_five_dvd_index_weylX_E8 [Finite K] (h5 : 5 ∣ Nat.card K - 1) :
    ¬ 5 ∣ (weylX .E8 K weylE8S).index := by
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  have hq5 := mod_eq_one_of_dvd_sub_one (by norm_num) hq h5
  have hG1 := geomSum_five_mod hq5
  have hG6 := geomSum_five_six_mod hq5
  have hq1 : (Nat.card K : ZMod 5) = 1 := cast_eq_one_of_dvd_sub_one hq h5
  have hm1 := cast_div_eq (p := 5) (c := 1) (by norm_num) (by norm_num) hG1
  have hm6 := cast_div_eq (p := 5) (c := 1) (by norm_num) (by norm_num) hG6
  have hGm1 : geomSum 5 1 (Nat.card K) = 5 * (geomSum 5 1 (Nat.card K) / 5) := by omega
  have hGm6 : geomSum 5 6 (Nat.card K) = 5 * (geomSum 5 6 (Nat.card K) / 5) := by omega
  rw [index_weylX_eq (M := Nat.card K ^ 120 * (geomSum 2 1 (Nat.card K) *
      geomSum 3 1 (Nat.card K) * geomSum 4 1 (Nat.card K) * (geomSum 5 1 (Nat.card K) / 5) *
      (geomSum 2 3 (Nat.card K) * geomSum 8 1 (Nat.card K)) *
      (geomSum 9 1 (Nat.card K) * geomSum 3 4 (Nat.card K)) *
      (geomSum 2 5 (Nat.card K) * geomSum 2 9 (Nat.card K) * geomSum 14 1 (Nat.card K)) *
      (geomSum 24 1 (Nat.card K) * geomSum 2 10 (Nat.card K) * (geomSum 5 6 (Nat.card K) / 5))))
    (by
      rw [card_adjointGroup_E8_eq, prodE8, card_weylE8S]
      nth_rewrite 1 [hGm1]
      nth_rewrite 1 [hGm6]
      ring)]
  apply not_dvd_of_cast_ne_zero
  push_cast
  simp only [hq1, hm1, hm6, geomSum_cast hq1, one_pow, Nat.cast_one]
  decide

end Index

theorem bigElemAbelianToralBar_E7_five : BigElemAbelianToralBar .E7 5 := by
  refine bigElemAbelianToralBar_of_finite Nat.prime_five (by norm_num) le_rfl
    fun K₁ _ _ _ hq A hA hcomm hpow hcard => ?_
  have h5 : 5 ∣ Nat.card K₁ - 1 := by simpa using hq
  refine exists_conj_torusGroup_of_weylX Nat.prime_five h5
    (isUnit_det_cartan_of_eq Nat.prime_five CFSG.LieType.Chevalley.det_cartan_E7 (by norm_num))
    (card_torusPow_E7 Nat.prime_five h5) (not_five_dvd_index_weylX_E7 h5) (fun s hs hs1 => ?_)
    hA hcomm hpow hcard
  obtain ⟨k, hk⟩ := exists_pow_eq_of_mem_zpowers Nat.prime_five orderOf_wordE7Five hs hs1
  refine ⟨k, wordE7Five, hk.symm, ?_⟩
  rw [Nat.card_zpowers, orderOf_wordE7Five]
  calc 5 * Nat.card {x : Fin Tag.E7.rank → ZMod 5 // torusWord .E7 5 wordE7Five x = x}
      ≤ 5 * 5 ^ (7 - 4) := Nat.mul_le_mul_left _ card_fix_wordE7Five_four
    _ < 5 ^ (Tag.E7.rank - 1) := by decide

theorem bigElemAbelianToralBar_E8_five : BigElemAbelianToralBar .E8 5 := by
  refine bigElemAbelianToralBar_of_finite Nat.prime_five (by norm_num) le_rfl
    fun K₁ _ _ _ hq A hA hcomm hpow hcard => ?_
  have h5 : 5 ∣ Nat.card K₁ - 1 := by simpa using hq
  refine exists_conj_torusGroup_of_weylX Nat.prime_five h5
    (isUnit_det_cartan_of_eq Nat.prime_five CFSG.LieType.Chevalley.det_cartan_E8 (by norm_num))
    (card_torusPow_E8 Nat.prime_five h5) (not_five_dvd_index_weylX_E8 h5) (fun s hs hs1 => ?_)
    hA hcomm hpow hcard
  rw [card_weylE8S]
  obtain ⟨k, hk | ⟨c, hc, hk⟩⟩ := exists_pow_eq_rep hs hs1
  · refine ⟨k, wordE8B, hk.symm, ?_⟩
    calc 25 * Nat.card {x : Fin Tag.E8.rank → ZMod 5 // torusWord .E8 5 wordE8B x = x}
        ≤ 25 * 5 ^ (8 - 4) := Nat.mul_le_mul_left _ card_fix_wordE8B_four
      _ < 5 ^ (Tag.E8.rank - 1) := by decide
  · refine ⟨k, wordE8AB c, by rw [wordProd_wordE8AB, hk], ?_⟩
    calc 25 * Nat.card {x : Fin Tag.E8.rank → ZMod 5 // torusWord .E8 5 (wordE8AB c) x = x}
        ≤ 25 * 5 ^ (8 - 4) := Nat.mul_le_mul_left _ (card_fix_wordE8AB_four hc)
      _ < 5 ^ (Tag.E8.rank - 1) := by decide

end CFSG.StandardType.ExcFramesHalf
