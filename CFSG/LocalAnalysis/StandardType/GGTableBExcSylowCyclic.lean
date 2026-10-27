module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcSylow
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTorus

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover
open CFSG.Timmesfeld.ExceptionalOrders (geomSum)

namespace TableBExc

local instance tableBExcNeZeroRankE7 : NeZero Tag.E7.rank := ⟨by decide⟩

local instance tableBExcNeZeroRankE8 : NeZero Tag.E8.rank := ⟨by decide⟩

local instance tableBExcFactFive : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

local instance tableBExcFactSeven : Fact (Nat.Prime 7) := ⟨by norm_num⟩

@[expose] def wordE7Five : List (Fin Tag.E7.rank) := [0, 2, 3, 4]

@[expose] def wordE7Seven : List (Fin Tag.E7.rank) := [0, 2, 3, 4, 5, 6]

@[expose] def wordE8Seven : List (Fin Tag.E8.rank) := [0, 2, 3, 4, 5, 6]

theorem orderOf_wordE7Five : orderOf ((coxeterSystem .E7).wordProd wordE7Five) = 5 :=
  orderOf_wordProd_eq Nat.prime_five _ (by decide +kernel) ⟨0, by decide +kernel⟩

theorem orderOf_wordE7Seven : orderOf ((coxeterSystem .E7).wordProd wordE7Seven) = 7 :=
  orderOf_wordProd_eq (by norm_num) _ (by decide +kernel) ⟨0, by decide +kernel⟩

theorem orderOf_wordE8Seven : orderOf ((coxeterSystem .E8).wordProd wordE8Seven) = 7 :=
  orderOf_wordProd_eq (by norm_num) _ (by decide +kernel) ⟨0, by decide +kernel⟩

theorem card_fix_wordE7Five :
    Nat.card {x : Fin Tag.E7.rank → ZMod 5 // torusWord .E7 5 wordE7Five x = x} ≤ 5 ^ (7 - 2) :=
  card_fix_torusWord_le (τ := .E7) wordE7Five ![0, 2] ![0, 1] (by decide)
    ![![2, 3], ![3, 3]] (by decide +kernel)

theorem card_fix_wordE7Seven :
    Nat.card {x : Fin Tag.E7.rank → ZMod 7 // torusWord .E7 7 wordE7Seven x = x} ≤ 7 ^ (7 - 2) :=
  card_fix_torusWord_le (τ := .E7) wordE7Seven ![0, 2] ![0, 1] (by decide)
    ![![3, 4], ![4, 4]] (by decide +kernel)

theorem card_fix_wordE8Seven :
    Nat.card {x : Fin Tag.E8.rank → ZMod 7 // torusWord .E8 7 wordE8Seven x = x} ≤ 7 ^ (8 - 2) :=
  card_fix_torusWord_le (τ := .E8) wordE8Seven ![0, 2] ![0, 1] (by decide)
    ![![3, 4], ![4, 4]] (by decide +kernel)

@[expose] def prodE7 (q : ℕ) : ℕ :=
  geomSum 2 1 q * geomSum 3 1 q * geomSum 4 1 q * geomSum 5 1 q *
    (geomSum 2 3 q * geomSum 8 1 q) * (geomSum 9 1 q * geomSum 3 4 q) *
      (geomSum 2 5 q * geomSum 2 9 q * geomSum 14 1 q)

@[expose] def prodE8 (q : ℕ) : ℕ :=
  geomSum 2 1 q * geomSum 3 1 q * geomSum 4 1 q * geomSum 5 1 q *
    (geomSum 2 3 q * geomSum 8 1 q) * (geomSum 9 1 q * geomSum 3 4 q) *
      (geomSum 2 5 q * geomSum 2 9 q * geomSum 14 1 q) *
        (geomSum 24 1 q * geomSum 2 10 q * geomSum 5 6 q)

theorem geomSum_five_mod {q : ℕ} (h : q % 5 = 1) : geomSum 5 1 q % 25 = 5 := by
  have hr : q % 25 = 1 ∨ q % 25 = 6 ∨ q % 25 = 11 ∨ q % 25 = 16 ∨ q % 25 = 21 := by omega
  rw [geomSum]
  simp only [one_mul]
  rw [TableBF4.geomSum_mod]
  rcases hr with h | h | h | h | h <;> rw [h] <;> decide

theorem geomSum_fourteen_mod {q : ℕ} (h : q % 7 = 1) : geomSum 14 1 q % 49 = 14 := by
  have hr : q % 49 = 1 ∨ q % 49 = 8 ∨ q % 49 = 15 ∨ q % 49 = 22 ∨ q % 49 = 29 ∨
      q % 49 = 36 ∨ q % 49 = 43 := by omega
  rw [geomSum]
  simp only [one_mul]
  rw [TableBF4.geomSum_mod]
  rcases hr with h | h | h | h | h | h | h <;> rw [h] <;> decide

theorem mod_eq_one_of_dvd_sub_one {p q : ℕ} (hp : 1 < p) (hq : 1 ≤ q) (h : p ∣ q - 1) :
    q % p = 1 := by
  obtain ⟨c, hc⟩ := h
  have : q = p * c + 1 := by omega
  rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt hp]

theorem cast_div_eq {p n c : ℕ} (hp : 1 < p) (hc : c < p) (h : n % (p * p) = p * c) :
    ((n / p : ℕ) : ZMod p) = c := by
  have h1 : n / p % p = c := by
    have hpos : 0 < p := by omega
    have e : n = p * p * (n / (p * p)) + p * c := by
      have := Nat.div_add_mod n (p * p)
      omega
    rw [e, show p * p * (n / (p * p)) + p * c = p * (p * (n / (p * p)) + c) by ring,
      Nat.mul_div_cancel_left _ hpos, Nat.mul_add_mod, Nat.mod_eq_of_lt hc]
  rw [← ZMod.natCast_mod, h1]

theorem not_dvd_of_cast_ne_zero {p M : ℕ} (h : (M : ZMod p) ≠ 0) : ¬ p ∣ M :=
  fun hd => h ((ZMod.natCast_eq_zero_iff M p).mpr hd)

section Orders

variable {K : Type} [Field K]

theorem card_adjointGroup_E8_eq [Finite K] :
    Nat.card (adjointGroup .E8 K) =
      Nat.card (torusGroup .E8 K) * (Nat.card K ^ 120 * prodE8 (Nat.card K)) := by
  rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E8,
    CFSG.Timmesfeld.ExceptionalOrders.card_torusGroup_E8,
    ← CFSG.Timmesfeld.ExceptionalOrders.ordE8_eq _ Nat.card_pos, prodE8, mul_assoc]

theorem card_adjointGroup_E7_eq [Finite K] [CharP K 2] :
    Nat.card (adjointGroup .E7 K) =
      Nat.card (torusGroup .E7 K) * (Nat.card K ^ 63 * prodE7 (Nat.card K)) := by
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  have hodd : Nat.gcd 2 (Nat.card K - 1) = 1 := by
    have : Fintype K := Fintype.ofFinite K
    have h0 : ((Fintype.card K : ℕ) : K) = 0 := FiniteField.cast_card_eq_zero K
    have h2 : 2 ∣ Nat.card K := by
      rw [Nat.card_eq_fintype_card]
      exact (CharP.cast_eq_zero_iff K 2 _).1 h0
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    have h3 : ¬ 2 ∣ Nat.card K - 1 := by omega
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 h3
  have hH : Nat.card (torusGroup .E7 K) = (Nat.card K - 1) ^ 7 := by
    have h := CFSG.Timmesfeld.ExceptionalOrders.card_torusGroup_E7 (K := K)
    rwa [Nat.gcd_comm, hodd, mul_one] at h
  rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E7, hH, CFSG.Open.ordE7, hodd,
    Nat.div_one, ← CFSG.Timmesfeld.ExceptionalOrders.ordE7_mul _ hq, prodE7, mul_assoc]

end Orders

section T

variable {K : Type} [Field K]

theorem ggExcToralRankInput_E7_five [Finite K] [CharP K 2] (h5 : 5 ∣ Nat.card K - 1) :
    GGExcToralRankInput .E7 K 5 := by
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  have hG := geomSum_five_mod (mod_eq_one_of_dvd_sub_one (by norm_num) hq h5)
  have hq1 : (Nat.card K : ZMod 5) = 1 := cast_eq_one_of_dvd_sub_one hq h5
  have hm1 := cast_div_eq (p := 5) (c := 1) (by norm_num) (by norm_num) hG
  have hGm : geomSum 5 1 (Nat.card K) = 5 * (geomSum 5 1 (Nat.card K) / 5) := by omega
  refine ggExcToralRankInput_of_cyclic Nat.prime_five h5
    (isUnit_det_cartan_of_eq Nat.prime_five det_cartan_E7 (by norm_num))
    (card_torusPow_E7 Nat.prime_five h5) wordE7Five orderOf_wordE7Five
    (M := Nat.card K ^ 63 * (geomSum 2 1 (Nat.card K) * geomSum 3 1 (Nat.card K) *
      geomSum 4 1 (Nat.card K) * (geomSum 5 1 (Nat.card K) / 5) *
      (geomSum 2 3 (Nat.card K) * geomSum 8 1 (Nat.card K)) *
      (geomSum 9 1 (Nat.card K) * geomSum 3 4 (Nat.card K)) *
      (geomSum 2 5 (Nat.card K) * geomSum 2 9 (Nat.card K) * geomSum 14 1 (Nat.card K))))
    ?_ ?_ ?_
  · rw [card_adjointGroup_E7_eq, prodE7]
    nth_rewrite 1 [hGm]
    ring
  · apply not_dvd_of_cast_ne_zero
    push_cast
    simp only [hq1, hm1, geomSum_cast hq1, one_pow, Nat.cast_one]
    decide
  · calc 5 * Nat.card {x : Fin Tag.E7.rank → ZMod 5 // torusWord .E7 5 wordE7Five x = x}
        ≤ 5 * 5 ^ (7 - 2) := Nat.mul_le_mul_left _ card_fix_wordE7Five
      _ < 5 ^ Tag.E7.rank := by decide

theorem ggExcToralRankInput_E7_seven [Finite K] [CharP K 2] (h7 : 7 ∣ Nat.card K - 1) :
    GGExcToralRankInput .E7 K 7 := by
  have hp7 : Nat.Prime 7 := by norm_num
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  have hG := geomSum_fourteen_mod (mod_eq_one_of_dvd_sub_one (by norm_num) hq h7)
  have hq1 : (Nat.card K : ZMod 7) = 1 := cast_eq_one_of_dvd_sub_one hq h7
  have hm2 := cast_div_eq (p := 7) (c := 2) (by norm_num) (by norm_num) hG
  have hGm : geomSum 14 1 (Nat.card K) = 7 * (geomSum 14 1 (Nat.card K) / 7) := by omega
  refine ggExcToralRankInput_of_cyclic hp7 h7
    (isUnit_det_cartan_of_eq hp7 det_cartan_E7 (by norm_num))
    (card_torusPow_E7 hp7 h7) wordE7Seven orderOf_wordE7Seven
    (M := Nat.card K ^ 63 * (geomSum 2 1 (Nat.card K) * geomSum 3 1 (Nat.card K) *
      geomSum 4 1 (Nat.card K) * geomSum 5 1 (Nat.card K) *
      (geomSum 2 3 (Nat.card K) * geomSum 8 1 (Nat.card K)) *
      (geomSum 9 1 (Nat.card K) * geomSum 3 4 (Nat.card K)) *
      (geomSum 2 5 (Nat.card K) * geomSum 2 9 (Nat.card K) * (geomSum 14 1 (Nat.card K) / 7))))
    ?_ ?_ ?_
  · rw [card_adjointGroup_E7_eq, prodE7]
    nth_rewrite 1 [hGm]
    ring
  · apply not_dvd_of_cast_ne_zero
    push_cast
    simp only [hq1, hm2, geomSum_cast hq1, one_pow]
    decide
  · calc 7 * Nat.card {x : Fin Tag.E7.rank → ZMod 7 // torusWord .E7 7 wordE7Seven x = x}
        ≤ 7 * 7 ^ (7 - 2) := Nat.mul_le_mul_left _ card_fix_wordE7Seven
      _ < 7 ^ Tag.E7.rank := by decide

theorem ggExcToralRankInput_E8_seven [Finite K] [CharP K 2] (h7 : 7 ∣ Nat.card K - 1) :
    GGExcToralRankInput .E8 K 7 := by
  have hp7 : Nat.Prime 7 := by norm_num
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  have hG := geomSum_fourteen_mod (mod_eq_one_of_dvd_sub_one (by norm_num) hq h7)
  have hq1 : (Nat.card K : ZMod 7) = 1 := cast_eq_one_of_dvd_sub_one hq h7
  have hm2 := cast_div_eq (p := 7) (c := 2) (by norm_num) (by norm_num) hG
  have hGm : geomSum 14 1 (Nat.card K) = 7 * (geomSum 14 1 (Nat.card K) / 7) := by omega
  refine ggExcToralRankInput_of_cyclic hp7 h7
    (isUnit_det_cartan_of_eq hp7 det_cartan_E8 (by norm_num))
    (card_torusPow_E8 hp7 h7) wordE8Seven orderOf_wordE8Seven
    (M := Nat.card K ^ 120 * (geomSum 2 1 (Nat.card K) * geomSum 3 1 (Nat.card K) *
      geomSum 4 1 (Nat.card K) * geomSum 5 1 (Nat.card K) *
      (geomSum 2 3 (Nat.card K) * geomSum 8 1 (Nat.card K)) *
      (geomSum 9 1 (Nat.card K) * geomSum 3 4 (Nat.card K)) *
      (geomSum 2 5 (Nat.card K) * geomSum 2 9 (Nat.card K) * (geomSum 14 1 (Nat.card K) / 7)) *
      (geomSum 24 1 (Nat.card K) * geomSum 2 10 (Nat.card K) * geomSum 5 6 (Nat.card K))))
    ?_ ?_ ?_
  · rw [card_adjointGroup_E8_eq, prodE8]
    nth_rewrite 1 [hGm]
    ring
  · apply not_dvd_of_cast_ne_zero
    push_cast
    simp only [hq1, hm2, geomSum_cast hq1, one_pow]
    decide
  · calc 7 * Nat.card {x : Fin Tag.E8.rank → ZMod 7 // torusWord .E8 7 wordE8Seven x = x}
        ≤ 7 * 7 ^ (8 - 2) := Nat.mul_le_mul_left _ card_fix_wordE8Seven
      _ < 7 ^ Tag.E8.rank := by decide

end T

end TableBExc

end CFSG.StandardType
