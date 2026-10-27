module

public import CFSG.Monster.Code.LatticeBasic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.Monster.Code

open CFSG.Monster
open scoped Finset

private theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

private theorem val_zero' : (0 : ZMod 2).val = 0 := rfl

private theorem val_one' : (1 : ZMod 2).val = 1 := rfl

private theorem bitLift_zero' : bitLift 0 = 0 := rfl

private theorem bitLift_one' : bitLift 1 = 1 := rfl

@[expose] def minVecs : Set (Fin 24 → ℤ) :=
  {u | u ∈ codeLattice C ∧ codeForm (fun i => (u i : ℚ)) (fun i => (u i : ℚ)) = 4}

@[expose] def minFamily₁ : Set (Fin 24 → ℤ) :=
  {u | #{i | u i ≠ 0} = 2 ∧ ∀ i, u i ≠ 0 → u i = 4 ∨ u i = -4}

@[expose] def minFamily₂ : Set (Fin 24 → ℤ) :=
  {u | ∃ d ∈ C, hammingNorm d = 8 ∧ (∀ i, d i ≠ 0 → u i = 2 ∨ u i = -2) ∧
    (∀ i, d i = 0 → u i = 0) ∧ Even #{i | u i = -2}}

@[expose] def oddMin (i : Fin 24) (d : Fin 24 → ZMod 2) : Fin 24 → ℤ :=
  fun j => (-1) ^ (d j).val * (1 - 4 * if j = i then 1 else 0)

@[expose] def minFamily₃ : Set (Fin 24 → ℤ) := {u | ∃ i : Fin 24, ∃ d ∈ C, u = oddMin i d}

theorem mem_minVecs_iff {u : Fin 24 → ℤ} : u ∈ minVecs ↔ u ∈ codeLattice C ∧ normSq u = 32 := by
  show (u ∈ codeLattice C ∧ _) ↔ _
  rw [codeForm_self_eq_four_iff]

private theorem odd_sq (x : ℤ) (hx : x % 2 = 1) : ∃ t, 0 ≤ t ∧ x * x = 1 + 8 * t := by
  obtain ⟨q, rfl⟩ : ∃ q, x = 2 * q + 1 := ⟨x / 2, by omega⟩
  obtain ⟨r, hr⟩ := Int.even_mul_succ_self q
  have hq : 0 ≤ q * (q + 1) := by
    rcases le_or_gt 0 q with h | h
    · positivity
    · nlinarith
  refine ⟨r, by linarith, ?_⟩
  linear_combination 4 * hr

private theorem sign_one (x : ℤ) (t : ZMod 2) (hx : x * x = 1)
    (hc : x ≡ 1 + 2 * bitLift t [ZMOD 4]) : x = (-1) ^ t.val := by
  have h : x = 1 ∨ x = -1 := mul_self_eq_one_iff.1 hx
  unfold Int.ModEq at hc
  rcases zmod2_cases t with rfl | rfl
  · rw [val_zero', pow_zero]; rw [bitLift_zero'] at hc; omega
  · rw [val_one', pow_one]; rw [bitLift_one'] at hc; omega

private theorem sign_three (x : ℤ) (t : ZMod 2) (hx : x * x = 9)
    (hc : x ≡ 1 + 2 * bitLift t [ZMOD 4]) : x = (-1) ^ t.val * (1 - 4) := by
  have h : x = 3 ∨ x = -3 := mul_self_eq_mul_self_iff.1 (by rw [hx]; norm_num)
  unfold Int.ModEq at hc
  rcases zmod2_cases t with rfl | rfl
  · rw [val_zero', pow_zero]; rw [bitLift_zero'] at hc; omega
  · rw [val_one', pow_one]; rw [bitLift_one'] at hc; omega

private theorem sq_par (x : ℤ) : (x * x - x) % 2 = 0 := by
  have h := Int.even_mul_pred_self x
  rw [Int.even_iff] at h
  have e : x * x - x = x * (x - 1) := by ring
  rw [e]
  exact h

private theorem exists_eq_one {t : Fin 24 → ℤ} (h0 : ∀ i, 0 ≤ t i) (h1 : ∑ i, t i = 1) :
    ∃ i₀, t i₀ = 1 ∧ ∀ j, j ≠ i₀ → t j = 0 := by
  obtain ⟨i₀, -, hi₀⟩ : ∃ i₀ ∈ Finset.univ, t i₀ ≠ 0 :=
    Finset.exists_ne_zero_of_sum_ne_zero (by rw [h1]; exact one_ne_zero)
  have hrest : 0 ≤ ∑ j ∈ Finset.univ.erase i₀, t j := Finset.sum_nonneg fun j _ => h0 j
  have hsplit := Finset.add_sum_erase Finset.univ t (Finset.mem_univ i₀)
  rw [h1] at hsplit
  have ht : t i₀ = 1 := by have := h0 i₀; omega
  refine ⟨i₀, ht, fun j hj => ?_⟩
  have hzero : ∑ j ∈ Finset.univ.erase i₀, t j = 0 := by omega
  exact (Finset.sum_eq_zero_iff_of_nonneg fun j _ => h0 j).1 hzero j
    (Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩)

theorem normSq_nonneg (u : Fin 24 → ℤ) : 0 ≤ normSq u :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (u i)

theorem normSq_pos {u : Fin 24 → ℤ} (h : u ≠ 0) : 0 < normSq u := by
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := Function.ne_iff.1 h
  have h1 : 0 < u i * u i := mul_self_pos.2 hi
  have h2 : u i * u i ≤ normSq u :=
    Finset.single_le_sum (f := fun i => u i * u i) (fun j _ => mul_self_nonneg (u j))
      (Finset.mem_univ i)
  linarith

theorem le_normSq (u : Fin 24 → ℤ) (i : Fin 24) : u i * u i ≤ normSq u :=
  Finset.single_le_sum (f := fun i => u i * u i) (fun j _ => mul_self_nonneg (u j))
    (Finset.mem_univ i)

theorem mem_minFamily₃_of_odd {u : Fin 24 → ℤ} {d : Fin 24 → ZMod 2} (hd : d ∈ C)
    (hud : ∀ i, u i ≡ 1 + 2 * bitLift (d i) [ZMOD 4]) (hn : normSq u = 32) :
    u ∈ minFamily₃ := by
  have hodd : ∀ i, u i % 2 = 1 := fun i => by
    have h := hud i
    unfold Int.ModEq at h
    have := bitLift_zero_or_one (d i)
    omega
  choose t ht0 ht using fun i => odd_sq (u i) (hodd i)
  have hsum : ∑ i, t i = 1 := by
    have h : normSq u = ∑ i, (1 + 8 * t i) := Finset.sum_congr rfl fun i _ => ht i
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hn] at h
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_ofNat, mul_one] at h
    omega
  obtain ⟨i₀, hi₀, hj⟩ := exists_eq_one ht0 hsum
  refine ⟨i₀, d, hd, funext fun j => ?_⟩
  by_cases hji : j = i₀
  · subst hji
    simp only [oddMin, ite_true, mul_one]
    exact sign_three _ _ (by rw [ht, hi₀]; norm_num) (hud _)
  · simp only [oddMin, hji, ite_false, mul_zero, sub_zero, mul_one]
    exact sign_one _ _ (by rw [ht, hj j hji]; norm_num) (hud j)

theorem mem_minFamily₁_of_four {u : Fin 24 → ℤ} (hu4 : ∀ i, u i % 4 = 0) (hn : normSq u = 32) :
    u ∈ minFamily₁ := by
  obtain ⟨w, hw⟩ : ∃ w : Fin 24 → ℤ, ∀ i, u i = 4 * w i :=
    ⟨fun i => u i / 4, fun i => by have := hu4 i; show u i = 4 * (u i / 4); omega⟩
  have hsum : ∑ i, w i * w i = 2 := by
    have h : normSq u = ∑ i, 16 * (w i * w i) :=
      Finset.sum_congr rfl fun i _ => by rw [hw i]; ring
    rw [← Finset.mul_sum, hn] at h
    omega
  have hbound : ∀ i, w i * w i ≤ 2 := fun i => by
    rw [← hsum]
    exact Finset.single_le_sum (f := fun i => w i * w i) (fun j _ => mul_self_nonneg _)
      (Finset.mem_univ i)
  have hval : ∀ i, w i = -1 ∨ w i = 0 ∨ w i = 1 := fun i => by
    have h := hbound i
    have h1 : w i ≤ 1 := by nlinarith
    have h2 : -1 ≤ w i := by nlinarith
    omega
  refine ⟨?_, fun i hi => ?_⟩
  · have hind : ∀ i, (if u i ≠ 0 then (1 : ℤ) else 0) = w i * w i := fun i => by
      rw [hw i]
      rcases hval i with h | h | h <;> rw [h] <;> norm_num
    have : ((#{i | u i ≠ 0} : ℕ) : ℤ) = 2 := by
      rw [Finset.natCast_card_filter, ← hsum]
      exact Finset.sum_congr rfl fun i _ => hind i
    exact_mod_cast this
  · rw [hw i] at hi ⊢
    rcases hval i with h | h | h
    · right; rw [h]; norm_num
    · exact absurd (by rw [h]; norm_num) hi
    · left; rw [h]; norm_num

theorem mem_minFamily₂_of_even {u : Fin 24 → ℤ} {d : Fin 24 → ZMod 2} (hd : d ∈ C) (hd0 : d ≠ 0)
    (hud : ∀ i, u i ≡ 2 * bitLift (d i) [ZMOD 4]) (hus : ∑ i, u i ≡ 0 [ZMOD 8])
    (hn : normSq u = 32) : u ∈ minFamily₂ := by
  have hw8 : 8 ≤ hammingNorm d := eight_le_wt hd hd0
  have hlow : ∀ i, 4 * bitLift (d i) ≤ u i * u i := fun i => by
    have h := hud i
    unfold Int.ModEq at h
    rcases bitLift_zero_or_one (d i) with hb | hb
    · rw [hb]; simpa using mul_self_nonneg (u i)
    · rw [hb] at h ⊢
      have : u i ≥ 2 ∨ u i ≤ -2 := by omega
      rcases this with h' | h' <;> nlinarith
  have hsumb : ∑ i, bitLift (d i) = hammingNorm d := sum_bitLift d
  have hzero : ∑ i, (u i * u i - 4 * bitLift (d i)) = 32 - 4 * hammingNorm d := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsumb]
    exact congrArg (· - _) hn
  have hnn : ∀ i, 0 ≤ u i * u i - 4 * bitLift (d i) := fun i => by linarith [hlow i]
  have hnonneg := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => hnn i
  have hwt : hammingNorm d = 8 := by
    have : (hammingNorm d : ℤ) ≤ 8 := by linarith
    exact_mod_cast le_antisymm this (by exact_mod_cast hw8)
  have heach : ∀ i, u i * u i = 4 * bitLift (d i) := fun i => by
    have h0 : ∑ i, (u i * u i - 4 * bitLift (d i)) = 0 := by rw [hzero, hwt]; norm_num
    have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hnn j).1 h0 i (Finset.mem_univ i)
    linarith
  have hon : ∀ i, d i ≠ 0 → u i = 2 ∨ u i = -2 := fun i hi => by
    have hb : bitLift (d i) = 1 := by
      rcases zmod2_cases (d i) with h | h
      · exact absurd h hi
      · rw [h]; rfl
    have h := heach i
    rw [hb] at h
    exact mul_self_eq_mul_self_iff.1 (by rw [h]; norm_num)
  have hoff : ∀ i, d i = 0 → u i = 0 := fun i hi => by
    have h := heach i
    rw [hi, bitLift_zero', mul_zero] at h
    exact mul_self_eq_zero.1 h
  refine ⟨d, hd, hwt, hon, hoff, ?_⟩
  have hcoord : ∀ i, u i = 2 * bitLift (d i) - 4 * (if u i = -2 then 1 else 0) := fun i => by
    rcases zmod2_cases (d i) with h | h
    · rw [hoff i h, h, bitLift_zero']; norm_num
    · rw [h, bitLift_one']
      rcases hon i (by rw [h]; exact one_ne_zero) with h' | h' <;> rw [h'] <;> norm_num
  have hs : ∑ i, u i = 16 - 4 * (#{i | u i = -2} : ℕ) := by
    rw [Finset.sum_congr rfl fun i _ => hcoord i, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, hsumb, hwt, Finset.natCast_card_filter]
    norm_num
  rw [hs] at hus
  unfold Int.ModEq at hus
  rw [Nat.even_iff]
  omega

theorem normSq_ge {u : Fin 24 → ℤ} (hu : u ∈ codeLattice C) (h0 : u ≠ 0) : 32 ≤ normSq u := by
  have h16 := sum_mul_self_emod_sixteen (C := C) (fun d hd => weight_mod_four hd) hu
  have hpos := normSq_pos h0
  have h16' : normSq u % 16 = 0 := h16
  rcases lt_or_ge (normSq u) 32 with hlt | hge
  swap
  · exact hge
  exfalso
  have hn : normSq u = 16 := by omega
  obtain ⟨m, hm, d, hd, hud, hus⟩ := hu
  rcases hm with rfl | rfl
  · by_cases hd0 : d = 0
    · subst hd0
      obtain ⟨w, hw⟩ : ∃ w : Fin 24 → ℤ, ∀ i, u i = 4 * w i := ⟨fun i => u i / 4, fun i => by
        have h := hud i
        unfold Int.ModEq at h
        simp only [Pi.zero_apply, bitLift_zero', mul_zero, add_zero] at h
        show u i = 4 * (u i / 4)
        omega⟩
      have hsq : ∑ i, w i * w i = 1 := by
        have h : normSq u = ∑ i, 16 * (w i * w i) :=
          Finset.sum_congr rfl fun i _ => by rw [hw i]; ring
        rw [← Finset.mul_sum, hn] at h
        omega
      have hpar : Even (∑ i, (w i * w i - w i)) :=
        Finset.even_sum _ fun i _ => Int.even_iff.2 (sq_par (w i))
      rw [Int.even_iff, Finset.sum_sub_distrib, hsq] at hpar
      have hs : ∑ i, u i = 4 * ∑ i, w i := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => hw i
      rw [hs, mul_zero] at hus
      unfold Int.ModEq at hus
      omega
    · have hw8 : 8 ≤ hammingNorm d := eight_le_wt hd hd0
      have hlow : ∀ i, 4 * bitLift (d i) ≤ u i * u i := fun i => by
        have h := hud i
        unfold Int.ModEq at h
        rcases bitLift_zero_or_one (d i) with hb | hb
        · rw [hb]; simpa using mul_self_nonneg (u i)
        · rw [hb] at h ⊢
          have : u i ≥ 2 ∨ u i ≤ -2 := by omega
          rcases this with h' | h' <;> nlinarith
      have h := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hlow i
      rw [← Finset.mul_sum, sum_bitLift] at h
      have : (8 : ℤ) ≤ hammingNorm d := by exact_mod_cast hw8
      change 4 * (hammingNorm d : ℤ) ≤ normSq u at h
      linarith
  · have hodd : ∀ i, u i % 2 = 1 := fun i => by
      have h := hud i
      unfold Int.ModEq at h
      have := bitLift_zero_or_one (d i)
      omega
    have h1 : ∀ i, 1 ≤ u i * u i := fun i => by
      obtain ⟨t, ht0, ht⟩ := odd_sq (u i) (hodd i)
      linarith
    have h := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h1 i
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_ofNat, mul_one] at h
    change (24 : ℤ) ≤ normSq u at h
    linarith

theorem mem_families_of_mem_minVecs {u : Fin 24 → ℤ} (hu : u ∈ minVecs) :
    u ∈ minFamily₁ ∪ minFamily₂ ∪ minFamily₃ := by
  obtain ⟨hL, hn⟩ := mem_minVecs_iff.1 hu
  obtain ⟨m, hm, d, hd, hud, hus⟩ := hL
  rcases hm with rfl | rfl
  · by_cases hd0 : d = 0
    · subst hd0
      refine Or.inl (Or.inl (mem_minFamily₁_of_four (fun i => ?_) hn))
      have h := hud i
      unfold Int.ModEq at h
      simpa [bitLift_zero'] using h
    · exact Or.inl (Or.inr (mem_minFamily₂_of_even hd hd0 (fun i => by simpa using hud i)
        (by simpa using hus) hn))
  · exact Or.inr (mem_minFamily₃_of_odd hd hud hn)

theorem minFamily₁_subset : minFamily₁ ⊆ minVecs := by
  rintro u ⟨hcard, hval⟩
  have hv : ∀ i, u i = 4 * (if u i = 4 then 1 else if u i = -4 then -1 else 0) := fun i => by
    by_cases h : u i = 0
    · simp [h]
    · rcases hval i h with h' | h' <;> simp [h']
  have hsq : ∀ i, u i * u i = 16 * (if u i ≠ 0 then 1 else 0) := fun i => by
    by_cases h : u i = 0
    · simp [h]
    · rcases hval i h with h' | h' <;> simp [h']
  have hn : normSq u = 32 := by
    rw [normSq, Finset.sum_congr rfl fun i _ => hsq i, ← Finset.mul_sum, ← Finset.natCast_card_filter,
      hcard]
    norm_num
  refine mem_minVecs_iff.2 ⟨⟨0, .inl rfl, 0, C.zero_mem, fun i => ?_, ?_⟩, hn⟩
  · simp only [Pi.zero_apply, bitLift_zero', mul_zero, add_zero]
    rw [hv i]
    exact Int.modEq_zero_iff_dvd.2 (Dvd.intro _ rfl)
  ·
    set s : Fin 24 → ℤ := fun i => if u i = 4 then 1 else if u i = -4 then -1 else 0
    have hs2 : ∀ i, s i * s i = if u i ≠ 0 then 1 else 0 := fun i => by
      by_cases h : u i = 0
      · simp [s, h]
      · rcases hval i h with h' | h' <;> simp [s, h']
    have hss : ∑ i, s i * s i = 2 := by
      rw [Finset.sum_congr rfl fun i _ => hs2 i, ← Finset.natCast_card_filter, hcard]
      norm_num
    have hpar : Even (∑ i, (s i * s i - s i)) :=
      Finset.even_sum _ fun i _ => Int.even_iff.2 (sq_par (s i))
    rw [Int.even_iff, Finset.sum_sub_distrib, hss] at hpar
    have hsum : ∑ i, u i = 4 * ∑ i, s i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => hv i
    rw [hsum]
    unfold Int.ModEq
    omega

theorem minFamily₂_subset : minFamily₂ ⊆ minVecs := by
  rintro u ⟨d, hd, hwt, hon, hoff, heven⟩
  have hsq : ∀ i, u i * u i = 4 * bitLift (d i) := fun i => by
    rcases zmod2_cases (d i) with h | h
    · rw [hoff i h, h, bitLift_zero']; norm_num
    · rw [h, bitLift_one']
      rcases hon i (by rw [h]; exact one_ne_zero) with h' | h' <;> rw [h'] <;> norm_num
  have hn : normSq u = 32 := by
    rw [normSq, Finset.sum_congr rfl fun i _ => hsq i, ← Finset.mul_sum, sum_bitLift, hwt]
    norm_num
  have hcoord : ∀ i, u i = 2 * bitLift (d i) - 4 * (if u i = -2 then 1 else 0) := fun i => by
    rcases zmod2_cases (d i) with h | h
    · rw [hoff i h, h, bitLift_zero']; norm_num
    · rw [h, bitLift_one']
      rcases hon i (by rw [h]; exact one_ne_zero) with h' | h' <;> rw [h'] <;> norm_num
  refine mem_minVecs_iff.2 ⟨⟨0, .inl rfl, d, hd, fun i => ?_, ?_⟩, hn⟩
  · rw [zero_add]
    unfold Int.ModEq
    rw [hcoord i]
    split_ifs <;> omega
  · have hs : ∑ i, u i = 16 - 4 * (#{i | u i = -2} : ℕ) := by
      rw [Finset.sum_congr rfl fun i _ => hcoord i, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum, sum_bitLift, hwt, Finset.natCast_card_filter]
      norm_num
    rw [hs, mul_zero]
    unfold Int.ModEq
    obtain ⟨k, hk⟩ := heven
    rw [hk]
    push_cast
    omega

private theorem neg_one_pow_val (t : ZMod 2) : ((-1 : ℤ) ^ t.val) = 1 - 2 * bitLift t := by
  rcases zmod2_cases t with rfl | rfl
  · rw [val_zero', bitLift_zero']; norm_num
  · rw [val_one', bitLift_one']; norm_num

theorem minFamily₃_subset : minFamily₃ ⊆ minVecs := by
  rintro u ⟨i, d, hd, rfl⟩
  have hcoord : ∀ j, oddMin i d j = (1 - 2 * bitLift (d j)) * (1 - 4 * if j = i then 1 else 0) :=
    fun j => by rw [oddMin, neg_one_pow_val]
  have hn : normSq (oddMin i d) = 32 := by
    have hsq : ∀ j, oddMin i d j * oddMin i d j = 1 + 8 * (if j = i then 1 else 0) := fun j => by
      rw [hcoord j]
      rcases bitLift_zero_or_one (d j) with hb | hb <;> rw [hb] <;> split_ifs <;> norm_num
    rw [normSq, Finset.sum_congr rfl fun j _ => hsq j, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp
  refine mem_minVecs_iff.2 ⟨⟨1, .inr rfl, d, hd, fun j => ?_, ?_⟩, hn⟩
  · unfold Int.ModEq
    rw [hcoord j]
    rcases bitLift_zero_or_one (d j) with hb | hb <;> rw [hb] <;> split_ifs <;> norm_num
  ·
    have hs : ∑ j, oddMin i d j = 24 - 2 * hammingNorm d - 4 * (1 - 2 * bitLift (d i)) := by
      have e : ∀ j, oddMin i d j =
          (1 - 2 * bitLift (d j)) - 4 * (if j = i then (1 - 2 * bitLift (d i)) else 0) := fun j => by
        rw [hcoord j]
        split_ifs with h
        · rw [h]; ring
        · ring
      rw [Finset.sum_congr rfl fun j _ => e j, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, sum_bitLift, ← Finset.mul_sum, Finset.sum_ite_eq']
      simp
    rw [hs]
    obtain ⟨k, hk⟩ := four_dvd_wt hd
    rw [hk]
    unfold Int.ModEq
    push_cast
    have := bitLift_zero_or_one (d i)
    omega

theorem minVecs_eq : minVecs = minFamily₁ ∪ minFamily₂ ∪ minFamily₃ := by
  refine Set.Subset.antisymm (fun u hu => mem_families_of_mem_minVecs hu) ?_
  rintro u ((h | h) | h)
  · exact minFamily₁_subset h
  · exact minFamily₂_subset h
  · exact minFamily₃_subset h

theorem minFamily₃_odd {u : Fin 24 → ℤ} (hu : u ∈ minFamily₃) : u 0 % 2 = 1 := by
  obtain ⟨i, d, -, rfl⟩ := hu
  rw [oddMin, neg_one_pow_val]
  rcases bitLift_zero_or_one (d 0) with hb | hb <;> rw [hb] <;> split_ifs <;> norm_num

theorem minFamily₁_even {u : Fin 24 → ℤ} (hu : u ∈ minFamily₁) (i : Fin 24) :
    u i = 0 ∨ u i = 4 ∨ u i = -4 := by
  by_cases h : u i = 0
  · exact Or.inl h
  · exact Or.inr (hu.2 i h)

theorem minFamily₂_even {u : Fin 24 → ℤ} (hu : u ∈ minFamily₂) (i : Fin 24) :
    u i = 0 ∨ u i = 2 ∨ u i = -2 := by
  obtain ⟨d, -, -, hon, hoff, -⟩ := hu
  by_cases h : d i = 0
  · exact Or.inl (hoff i h)
  · exact Or.inr (hon i h)

theorem disjoint_minFamily₁₂ : Disjoint minFamily₁ minFamily₂ := by
  rw [Set.disjoint_left]
  intro u h1 h2
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    have hne : (Finset.univ.filter fun i => u i ≠ 0).Nonempty :=
      Finset.card_pos.1 (by rw [h1.1]; norm_num)
    obtain ⟨i, hi⟩ := hne
    exact ⟨i, (Finset.mem_filter.1 hi).2⟩
  rcases h1.2 i hi with h | h <;> rcases minFamily₂_even h2 i with h' | h' | h' <;> omega

theorem disjoint_minFamily₁₃ : Disjoint minFamily₁ minFamily₃ := by
  rw [Set.disjoint_left]
  intro u h1 h3
  have := minFamily₃_odd h3
  rcases minFamily₁_even h1 0 with h | h | h <;> rw [h] at this <;> norm_num at this

theorem disjoint_minFamily₂₃ : Disjoint minFamily₂ minFamily₃ := by
  rw [Set.disjoint_left]
  intro u h2 h3
  have := minFamily₃_odd h3
  rcases minFamily₂_even h2 0 with h | h | h <;> rw [h] at this <;> norm_num at this

end CFSG.Monster.Code
