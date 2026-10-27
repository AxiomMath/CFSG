module

public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup

private theorem s16h_e3_tt_mem_of_pow_nine {Y : Type} [Group Y]
    {X : Subgroup Y} [hN : X.Normal] (hP : IsPGroup 2 (Y ⧸ X)) {y : Y}
    (hy : y ^ 9 = 1) : y ∈ X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq9 : (QuotientGroup.mk' X y) ^ 9 = 1 := by
    rw [← map_pow, hy, map_one]
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP) (QuotientGroup.mk' X y)
  have hdvd : orderOf (QuotientGroup.mk' X y) ∣ 9 := orderOf_dvd_of_pow_eq_one hq9
  have h2k : 2 ^ k ∣ 9 := hk ▸ hdvd
  have hcop : Nat.Coprime (2 ^ k) 9 := (by norm_num : Nat.Coprime 2 9).pow_left k
  have h1 : 2 ^ k = 1 := by
    have hg : Nat.gcd (2 ^ k) 9 = 1 := Nat.coprime_iff_gcd_eq_one.mp hcop
    rwa [Nat.gcd_eq_left h2k] at hg
  have hq1 : QuotientGroup.mk' X y = 1 := orderOf_eq_one_iff.mp (hk.trans h1)
  exact (QuotientGroup.eq_one_iff y).mp hq1

theorem s16h_e3_two_three_parabolic_of_normalized {W : Type} [Group W] [Finite W]
    {X T B : Subgroup W} (hTX : T ≤ X) (hBX : B ≤ X) (hT2 : IsPGroup 2 ↥T)
    (hBcard : Nat.card ↥B = 2 ^ 6 * 9) (hBexp : ∀ b ∈ B, b ^ 24 = 1)
    (hBT : T ≤ Subgroup.normalizer (B : Set W)) :
    ∃ (J : Subgroup W) (a : ℕ), J ≤ X ∧ T ≤ J ∧ Nat.card ↥J = 2 ^ a * 9 ∧
      ∀ x ∈ J, x ^ 9 = 1 → x ^ 3 = 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set J : Subgroup W := B ⊔ T with hJdef
  have hBJ : B ≤ J := le_sup_left
  have hTJ : T ≤ J := le_sup_right
  have hJX : J ≤ X := sup_le hBX hTX
  have hBnorm : (B.subgroupOf J).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBJ).mpr
      (by rw [hJdef]; exact sup_le Subgroup.le_normalizer hBT)
  haveI : (B.subgroupOf J).Normal := hBnorm
  obtain ⟨j, hj⟩ := (hT2.to_inf_right (H := B)).exists_card_eq
  obtain ⟨k, hk⟩ := hT2.exists_card_eq
  have hBrelJ : B.relIndex J = B.relIndex T := by
    rw [hJdef, sup_comm]
    exact CFSG.Quasithin.A4.relIndex_sup_eq_of_le_normalizer' hBT
  have hquot : IsPGroup 2 (↥J ⧸ B.subgroupOf J) := by
    have hdvd : Nat.card (↥J ⧸ B.subgroupOf J) ∣ 2 ^ k := by
      have hcard : Nat.card (↥J ⧸ B.subgroupOf J) = B.relIndex J := rfl
      rw [hcard, hBrelJ, ← hk]
      exact ⟨Nat.card ↥(B ⊓ T), (Subgroup.relIndex_mul_card B T).symm⟩
    exact IsPGroup.of_card_dvd_pow hdvd
  have hJ_eq : Nat.card ↥J = B.relIndex T * Nat.card ↥B := by
    have h3 := Subgroup.relIndex_mul_card B (T ⊔ B)
    rw [inf_eq_left.mpr le_sup_right, CFSG.Quasithin.A4.relIndex_sup_eq_of_le_normalizer' hBT] at h3
    rw [hJdef, sup_comm]
    exact h3.symm
  have hJcard_mul : Nat.card ↥J * 2 ^ j = 2 ^ k * (2 ^ 6 * 9) := by
    rw [hJ_eq, hBcard]
    have h2 : B.relIndex T * 2 ^ j = 2 ^ k := by
      have h := Subgroup.relIndex_mul_card B T
      rwa [hj, hk] at h
    calc (B.relIndex T * (2 ^ 6 * 9)) * 2 ^ j = (B.relIndex T * 2 ^ j) * (2 ^ 6 * 9) := by
          ring
      _ = 2 ^ k * (2 ^ 6 * 9) := by rw [h2]
  have hjle : j ≤ k := by
    have hdvd : 2 ^ j ∣ 2 ^ k := by
      rw [← hj, ← hk]
      exact Subgroup.card_dvd_of_le (inf_le_right : B ⊓ T ≤ T)
    exact (Nat.pow_le_pow_iff_right (by norm_num : 2 ≤ 2)).mp
      (Nat.le_of_dvd (by positivity) hdvd)
  have hJcard : Nat.card ↥J = 2 ^ (k + 6 - j) * 9 := by
    have hRHS : 2 ^ k * (2 ^ 6 * 9) = (2 ^ (k + 6 - j) * 9) * 2 ^ j := by
      have hpow : 2 ^ (k + 6 - j) * 2 ^ j = 2 ^ (k + 6) := by
        rw [← pow_add, Nat.sub_add_cancel (by omega : j ≤ k + 6)]
      rw [← mul_assoc, ← pow_add, ← hpow]
      ac_rfl
    rw [hRHS] at hJcard_mul
    exact Nat.mul_right_cancel (by positivity : 0 < 2 ^ j) hJcard_mul
  refine ⟨J, k + 6 - j, hJX, hTJ, hJcard, ?_⟩
  intro x hxJ hx9
  have hxJ9 : (⟨x, hxJ⟩ : ↥J) ^ 9 = 1 := Subtype.ext (by simpa using hx9)
  have hxB : x ∈ B := by
    have hxBsub : (⟨x, hxJ⟩ : ↥J) ∈ B.subgroupOf J :=
      s16h_e3_tt_mem_of_pow_nine hquot hxJ9
    exact Subgroup.mem_subgroupOf.mp hxBsub
  have hx24 : x ^ 24 = 1 := hBexp x hxB
  have hd9 : orderOf x ∣ 9 := orderOf_dvd_of_pow_eq_one hx9
  have hd24 : orderOf x ∣ 24 := orderOf_dvd_of_pow_eq_one hx24
  have hd3 : orderOf x ∣ 3 := by
    have h := Nat.dvd_gcd hd9 hd24
    norm_num at h
    exact h
  exact orderOf_dvd_iff_pow_eq_one.mp hd3

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
