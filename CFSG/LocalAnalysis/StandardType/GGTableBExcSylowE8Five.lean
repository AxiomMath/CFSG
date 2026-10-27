module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcSylowCyclic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover
open CFSG.Timmesfeld.ExceptionalOrders (geomSum)
open scoped Pointwise

namespace TableBExc

local instance tableBExcFiveNeZeroRankE8 : NeZero Tag.E8.rank := ⟨by decide⟩

local instance tableBExcFiveFact : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

@[expose] def wordE8A : List (Fin Tag.E8.rank) := [0, 2, 3, 1]

@[expose] def wordE8B : List (Fin Tag.E8.rank) :=
  [4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1,
    3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7]

@[expose] def weylE8A : WeylGroup .E8 := (coxeterSystem .E8).wordProd wordE8A

@[expose] def weylE8B : WeylGroup .E8 := (coxeterSystem .E8).wordProd wordE8B

theorem orderOf_weylE8A : orderOf weylE8A = 5 :=
  orderOf_wordProd_eq Nat.prime_five _ (by decide +kernel) ⟨0, by decide +kernel⟩

theorem orderOf_weylE8B : orderOf weylE8B = 5 :=
  orderOf_wordProd_eq Nat.prime_five _ (by decide +kernel) ⟨4, by decide +kernel⟩

theorem weylE8A_mul_weylE8B : weylE8A * weylE8B = weylE8B * weylE8A := by
  refine ext_single fun i => ?_
  rw [mul_smul, mul_smul, weylE8A, weylE8B, wordProd_smul, wordProd_smul, wordProd_smul,
    wordProd_smul]
  revert i
  decide +kernel

theorem weylE8A_pow_smul (a : ℕ) :
    weylE8A ^ a • (Pi.single 7 1 : Fin Tag.E8.rank → ℤ) = Pi.single 7 1 := by
  induction a with
  | zero => rw [pow_zero, one_smul]
  | succ a ih =>
    rw [pow_succ, mul_smul, weylE8A, wordProd_smul,
      show wordAct .E8 wordE8A (Pi.single 7 1) = Pi.single 7 1 by decide +kernel]
    exact ih

theorem weylE8B_ne_pow (a : ℕ) : weylE8B ≠ weylE8A ^ a := by
  intro h
  have h1 := weylE8A_pow_smul a
  rw [← h, weylE8B, wordProd_smul] at h1
  revert h1
  decide +kernel

@[expose] def weylE8S : Subgroup (WeylGroup .E8) :=
  Subgroup.zpowers weylE8A ⊔ Subgroup.zpowers weylE8B

theorem zpowers_weylE8B_le_normalizer :
    Subgroup.zpowers weylE8B ≤
      Subgroup.normalizer (Subgroup.zpowers weylE8A : Set (WeylGroup .E8)) := by
  intro y hy
  apply Subgroup.centralizer_le_normalizer
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact (Commute.zpow_zpow (weylE8A_mul_weylE8B : Commute weylE8A weylE8B) k m).eq

theorem exists_pow_eq_zpow_of_orderOf_five {w : WeylGroup .E8} (hw : orderOf w = 5) (k : ℤ) :
    ∃ a : ℕ, a < 5 ∧ w ^ k = w ^ a := by
  have h := (zpow_mod_orderOf w k).symm
  rw [hw] at h
  have h0 : 0 ≤ k % 5 := Int.emod_nonneg k (by norm_num)
  have h5 : k % 5 < 5 := Int.emod_lt_of_pos k (by norm_num)
  refine ⟨(k % 5).toNat, by omega, ?_⟩
  rw [h, ← zpow_natCast, Int.toNat_of_nonneg h0]
  norm_num

theorem disjoint_zpowers_weylE8 :
    Disjoint (Subgroup.zpowers weylE8A) (Subgroup.zpowers weylE8B) := by
  have hdvd : Nat.card (Subgroup.zpowers weylE8A ⊓ Subgroup.zpowers weylE8B : Subgroup _) ∣ 5 := by
    have := Subgroup.card_dvd_of_le
      (inf_le_right : Subgroup.zpowers weylE8A ⊓ Subgroup.zpowers weylE8B ≤ _)
    rwa [Nat.card_zpowers, orderOf_weylE8B] at this
  rcases (Nat.dvd_prime Nat.prime_five).mp hdvd with h1 | h1
  · rw [disjoint_iff]
    exact Subgroup.eq_bot_of_card_eq _ h1
  · exfalso
    have : Finite (Subgroup.zpowers weylE8B) := by
      refine Nat.finite_of_card_ne_zero ?_
      rw [Nat.card_zpowers, orderOf_weylE8B]
      norm_num
    have heq : Subgroup.zpowers weylE8A ⊓ Subgroup.zpowers weylE8B = Subgroup.zpowers weylE8B :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h1, Nat.card_zpowers, orderOf_weylE8B])
    have hmem : weylE8B ∈ Subgroup.zpowers weylE8A ⊓ Subgroup.zpowers weylE8B := by
      rw [heq]
      exact Subgroup.mem_zpowers _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem.1
    obtain ⟨a, -, ha'⟩ := exists_pow_eq_zpow_of_orderOf_five orderOf_weylE8A k
    rw [ha'] at hk
    exact weylE8B_ne_pow a hk.symm

theorem card_weylE8S : Nat.card weylE8S = 25 := by
  rw [weylE8S, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _
    zpowers_weylE8B_le_normalizer disjoint_zpowers_weylE8, Nat.card_zpowers, Nat.card_zpowers,
    orderOf_weylE8A, orderOf_weylE8B]

theorem exists_eq_of_mem_weylE8S {w : WeylGroup .E8} (hw : w ∈ weylE8S) :
    ∃ a b : ℕ, a < 5 ∧ b < 5 ∧ w = weylE8A ^ a * weylE8B ^ b := by
  have h := Subgroup.coe_mul_of_right_le_normalizer_left _ _ zpowers_weylE8B_le_normalizer
  have hw' : w ∈ (Subgroup.zpowers weylE8A : Set (WeylGroup .E8)) *
      (Subgroup.zpowers weylE8B : Set (WeylGroup .E8)) := by
    rw [← h]
    exact hw
  obtain ⟨x, hx, y, hy, rfl⟩ := hw'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  obtain ⟨a, ha, ha'⟩ := exists_pow_eq_zpow_of_orderOf_five orderOf_weylE8A k
  obtain ⟨b, hb, hb'⟩ := exists_pow_eq_zpow_of_orderOf_five orderOf_weylE8B m
  exact ⟨a, b, ha, hb, by rw [ha', hb']⟩

theorem exists_mul_mod_five_eq_one {a : ℕ} (ha0 : a ≠ 0) (ha : a < 5) :
    ∃ k : ℕ, a * k % 5 = 1 := by
  interval_cases a
  · exact absurd rfl ha0
  · exact ⟨1, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨4, rfl⟩

theorem commute_weylE8 : Commute weylE8A weylE8B := by
  unfold Commute SemiconjBy
  exact weylE8A_mul_weylE8B

theorem exists_pow_eq_rep {s : WeylGroup .E8} (hs : s ∈ weylE8S) (hs1 : s ≠ 1) :
    ∃ k : ℕ, s ^ k = weylE8B ∨ ∃ c : ℕ, c < 5 ∧ s ^ k = weylE8A * weylE8B ^ c := by
  obtain ⟨a, b, ha, hb, hab⟩ := exists_eq_of_mem_weylE8S hs
  rw [hab] at hs1 ⊢
  have hcomm : Commute (weylE8A ^ a) (weylE8B ^ b) := commute_weylE8.pow_pow a b
  by_cases ha0 : a = 0
  · subst ha0
    have hb0 : b ≠ 0 := by
      rintro rfl
      exact hs1 (by rw [pow_zero, pow_zero, one_mul])
    obtain ⟨k, hk⟩ := exists_mul_mod_five_eq_one hb0 hb
    refine ⟨k, Or.inl ?_⟩
    rw [pow_zero, one_mul, ← pow_mul, ← pow_mod_orderOf, orderOf_weylE8B, hk, pow_one]
  · obtain ⟨k, hk⟩ := exists_mul_mod_five_eq_one ha0 ha
    refine ⟨k, Or.inr ⟨b * k % 5, Nat.mod_lt _ (by norm_num), ?_⟩⟩
    rw [hcomm.mul_pow, ← pow_mul, ← pow_mul, ← pow_mod_orderOf weylE8A, orderOf_weylE8A, hk,
      pow_one, ← pow_mod_orderOf weylE8B, orderOf_weylE8B]

@[expose] def wordE8AB (c : ℕ) : List (Fin Tag.E8.rank) :=
  wordE8A ++ (List.replicate c wordE8B).flatten

theorem wordProd_wordE8AB (c : ℕ) :
    (coxeterSystem .E8).wordProd (wordE8AB c) = weylE8A * weylE8B ^ c := by
  rw [wordE8AB, CoxeterSystem.wordProd_append, wordProd_replicate]
  rfl

theorem card_fix_wordE8B :
    Nat.card {x : Fin Tag.E8.rank → ZMod 5 // torusWord .E8 5 wordE8B x = x} ≤ 5 ^ (8 - 3) :=
  card_fix_torusWord_le (τ := .E8) wordE8B ![0, 5, 6] ![4, 5, 7] (by decide)
    ![![4, 1, 1], ![1, 0, 1], ![2, 0, 0]] (by decide +kernel)

theorem minor_wordE8AB : ∀ c : Fin 5, ∀ a b : Fin 3,
    ∑ d, (![![4, 3, 0], ![0, 2, 0], ![4, 1, 4]] : Fin 3 → Fin 3 → ZMod 5) a d *
      (torusWord .E8 5 (wordE8AB c) (Pi.single ((![0, 1, 2] : Fin 3 → Fin Tag.E8.rank) b) 1)
        ((![0, 1, 2] : Fin 3 → Fin Tag.E8.rank) d) -
        if (![0, 1, 2] : Fin 3 → Fin Tag.E8.rank) d = (![0, 1, 2] : Fin 3 → Fin Tag.E8.rank) b
        then 1 else 0) = if a = b then 1 else 0 := by
  decide +kernel

theorem card_fix_wordE8AB {c : ℕ} (hc : c < 5) :
    Nat.card {x : Fin Tag.E8.rank → ZMod 5 // torusWord .E8 5 (wordE8AB c) x = x} ≤
      5 ^ (8 - 3) :=
  card_fix_torusWord_le (τ := .E8) (wordE8AB c) ![0, 1, 2] ![0, 1, 2] (by decide)
    ![![4, 3, 0], ![0, 2, 0], ![4, 1, 4]] (minor_wordE8AB ⟨c, hc⟩)

theorem geomSum_five_six_mod {q : ℕ} (h : q % 5 = 1) : geomSum 5 6 q % 25 = 5 := by
  have e : geomSum 5 6 q = geomSum 5 1 (q ^ 6) := by
    simp only [geomSum, one_mul, ← pow_mul]
  rw [e]
  refine geomSum_five_mod ?_
  rw [Nat.pow_mod, h]

section T

variable {K : Type} [Field K]

theorem ggExcToralRankInput_E8_five [Finite K] [CharP K 2] (h5 : 5 ∣ Nat.card K - 1) :
    GGExcToralRankInput .E8 K 5 := by
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  have hq5 := mod_eq_one_of_dvd_sub_one (by norm_num) hq h5
  have hG1 := geomSum_five_mod hq5
  have hG6 := geomSum_five_six_mod hq5
  have hq1 : (Nat.card K : ZMod 5) = 1 := cast_eq_one_of_dvd_sub_one hq h5
  have hm1 := cast_div_eq (p := 5) (c := 1) (by norm_num) (by norm_num) hG1
  have hm6 := cast_div_eq (p := 5) (c := 1) (by norm_num) (by norm_num) hG6
  have hGm1 : geomSum 5 1 (Nat.card K) = 5 * (geomSum 5 1 (Nat.card K) / 5) := by omega
  have hGm6 : geomSum 5 6 (Nat.card K) = 5 * (geomSum 5 6 (Nat.card K) / 5) := by omega
  set M := Nat.card K ^ 120 * (geomSum 2 1 (Nat.card K) * geomSum 3 1 (Nat.card K) *
      geomSum 4 1 (Nat.card K) * (geomSum 5 1 (Nat.card K) / 5) *
      (geomSum 2 3 (Nat.card K) * geomSum 8 1 (Nat.card K)) *
      (geomSum 9 1 (Nat.card K) * geomSum 3 4 (Nat.card K)) *
      (geomSum 2 5 (Nat.card K) * geomSum 2 9 (Nat.card K) * geomSum 14 1 (Nat.card K)) *
      (geomSum 24 1 (Nat.card K) * geomSum 2 10 (Nat.card K) * (geomSum 5 6 (Nat.card K) / 5)))
    with hM
  have hC : Nat.card (adjointGroup .E8 K) =
      Nat.card weylE8S * Nat.card (torusGroup .E8 K) * M := by
    rw [card_adjointGroup_E8_eq, prodE8, card_weylE8S, hM]
    nth_rewrite 1 [hGm1]
    nth_rewrite 1 [hGm6]
    ring
  have hMp : ¬ 5 ∣ M := by
    apply not_dvd_of_cast_ne_zero
    rw [hM]
    push_cast
    simp only [hq1, hm1, hm6, geomSum_cast hq1, one_pow, Nat.cast_one]
    decide
  refine ggExcToralRankInput_of_weylX Nat.prime_five h5
    (isUnit_det_cartan_of_eq Nat.prime_five det_cartan_E8 (by norm_num))
    (card_torusPow_E8 Nat.prime_five h5) (S := weylE8S)
    (by rw [index_weylX_eq hC]; exact hMp) fun s hs hs1 => ?_
  obtain ⟨k, hk | ⟨c, hc, hk⟩⟩ := exists_pow_eq_rep hs hs1
  · refine ⟨k, wordE8B, hk.symm, ?_⟩
    rw [card_weylE8S]
    calc 25 * Nat.card {x : Fin Tag.E8.rank → ZMod 5 // torusWord .E8 5 wordE8B x = x}
        ≤ 25 * 5 ^ (8 - 3) := Nat.mul_le_mul_left _ card_fix_wordE8B
      _ < 5 ^ Tag.E8.rank := by decide
  · refine ⟨k, wordE8AB c, by rw [wordProd_wordE8AB, hk], ?_⟩
    rw [card_weylE8S]
    calc 25 * Nat.card {x : Fin Tag.E8.rank → ZMod 5 // torusWord .E8 5 (wordE8AB c) x = x}
        ≤ 25 * 5 ^ (8 - 3) := Nat.mul_le_mul_left _ (card_fix_wordE8AB hc)
      _ < 5 ^ Tag.E8.rank := by decide

end T

end TableBExc

end CFSG.StandardType
