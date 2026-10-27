module

public import CFSG.RankThree.GroupTheory.SteinbergBMFrattiniNormalizerTwoCore

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBM

open Subgroup
open scoped Pointwise

variable {C : Type*} [Group C]

theorem eq_bot_of_isPGroup_two_of_le_odd [Finite C] {H L : Subgroup C} (hH : IsPGroup 2 H)
    (hHL : H ≤ L) (hL : Odd (Nat.card L)) : H = ⊥ := by
  obtain ⟨k, hk⟩ := hH.exists_card_eq
  have hdvd : 2 ^ k ∣ Nat.card L := hk ▸ card_dvd_of_le hHL
  rcases k with _ | k
  · rw [pow_zero] at hk
    exact eq_bot_of_card_eq H hk
  · exact absurd ((dvd_pow_self 2 (Nat.succ_ne_zero k)).trans hdvd)
      (Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hL))

theorem small_two_sylow_normal_prime_complement_odd [Finite C] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hp7 : p ≠ 7) {b : C} (hb : orderOf b = p)
    (hodd : Odd (Nat.card (centralizer ({b} : Set C))))
    (hsyl : ∃ T : Sylow 2 C, Nat.card T ≤ 8) {K : Subgroup C} (hK : K.Normal)
    (hpK : ¬ p ∣ Nat.card K) : Odd (Nat.card K) := by
  have : Fact p.Prime := ⟨hp⟩
  set Z := zpowers b with hZdef
  have hZp : IsPGroup p Z := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb, pow_one])
  have hZK : Z ≤ normalizer (K : Set C) := by
    rw [normalizer_eq_top_iff.mpr hK]
    exact le_top
  let : MulDistribMulAction Z K := MulDistribMulAction.compHom K (inclusion hZK)
  have hsmulK : ∀ (g : Z) (k : K), ((g • k : K) : C) = g * k * (g : C)⁻¹ := fun _ _ => rfl
  obtain ⟨B, hB⟩ : ∃ B : Sylow 2 K, ∀ g : Z, g • B = B := by
    have hcong := hZp.card_modEq_card_fixedPoints (Sylow 2 K)
    obtain ⟨P⟩ : Nonempty (Sylow 2 K) := inferInstance
    have hdvd : ¬ p ∣ Nat.card (Sylow 2 K) := fun h =>
      hpK (h.trans (P.card_dvd_index.trans (index_dvd_card _)))
    by_contra hnone
    push Not at hnone
    have h0 : Nat.card (MulAction.fixedPoints Z (Sylow 2 K)) = 0 := by
      rw [Nat.card_eq_zero]
      left
      exact ⟨fun ⟨Q, hQ⟩ => by
        obtain ⟨g, hg⟩ := hnone Q
        exact hg (hQ g)⟩
    rw [h0] at hcong
    exact hdvd (Nat.modEq_zero_iff_dvd.mp hcong)
  set B' : Subgroup C := (B : Subgroup K).map K.subtype with hB'def
  have hB'2 : IsPGroup 2 B' := B.isPGroup'.map _
  have hZB' : Z ≤ normalizer (B' : Set C) := by
    refine le_normalizer_of_forall_conj_mem fun g hg x hx => ?_
    obtain ⟨k, hk, rfl⟩ := hx
    have heq : (⟨g, hg⟩ : Z) • (B : Subgroup K) = (B : Subgroup K) := by
      rw [← Sylow.pointwise_smul_def, hB]
    have hmem : (⟨g, hg⟩ : Z) • k ∈ (B : Subgroup K) := by
      rw [← heq]
      exact smul_mem_pointwise_smul k _ _ hk
    exact ⟨_, hmem, hsmulK _ k⟩
  let : MulDistribMulAction Z B' := MulDistribMulAction.compHom B' (inclusion hZB')
  have hsmulB : ∀ (g : Z) (x : B'), ((g • x : B') : C) = g * x * (g : C)⁻¹ := fun _ _ => rfl
  have hcong := hZp.card_modEq_card_fixedPoints B'
  have hfix : Nat.card (MulAction.fixedPoints Z B') = 1 := by
    rw [Nat.card_eq_one_iff_exists]
    refine ⟨⟨1, fun g => smul_one g⟩, fun ⟨y, hy⟩ => ?_⟩
    apply Subtype.ext
    change y = 1
    have h := congrArg Subtype.val (hy ⟨b, mem_zpowers b⟩)
    rw [hsmulB] at h
    have hyc : (y : C) ∈ centralizer ({b} : Set C) := by
      rw [mem_centralizer_singleton_iff]
      calc (y : C) * b = b * (y : C) * b⁻¹ * b := by rw [h]
        _ = b * y := by group
    have hbot := eq_bot_of_isPGroup_two_of_le_odd (H := B' ⊓ centralizer ({b} : Set C))
      (hB'2.to_le inf_le_left) inf_le_right hodd
    have hy1 : (y : C) = 1 := (mem_bot.mp (hbot ▸ (⟨y.2, hyc⟩ : (y : C) ∈ B' ⊓ _)))
    exact Subtype.ext hy1
  rw [hfix] at hcong
  obtain ⟨T, hT⟩ := hsyl
  obtain ⟨T', hT'⟩ := hB'2.exists_le_sylow
  have hT'card : Nat.card T' = Nat.card T := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  have hle8 : Nat.card B' ≤ 8 := (card_le_of_le hT').trans (hT'card ▸ hT)
  obtain ⟨k, hk⟩ := hB'2.exists_card_eq
  rw [hk] at hcong hle8
  have hk3 : k ≤ 3 := by
    by_contra h
    have : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hk0 : k = 0 := by
    have hdvd : p ∣ 2 ^ k - 1 := (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp hcong.symm
    interval_cases k
    · rfl
    · exact absurd (Nat.le_of_dvd (by norm_num) hdvd) (by omega)
    · exact absurd (Nat.le_of_dvd (by norm_num) hdvd) (by omega)
    · have h7' : p ∣ 7 := by simpa using hdvd
      have h7 : p ≤ 7 := Nat.le_of_dvd (by norm_num) h7'
      interval_cases p <;> omega
  have hB1 : Nat.card B = 1 := by
    rw [← card_map_of_injective K.subtype_injective]
    change Nat.card B' = 1
    rw [hk, hk0, pow_zero]
  have hfac : (Nat.card K).factorization 2 = 0 := by
    have h := Sylow.card_eq_multiplicity B
    rw [hB1] at h
    exact (Nat.pow_eq_one.mp h.symm).resolve_left (by norm_num)
  have h2 : ¬ 2 ∣ Nat.card K := by
    rw [Nat.factorization_eq_zero_iff] at hfac
    rcases hfac with h | h | h
    · exact absurd Nat.prime_two h
    · exact h
    · exact absurd h Nat.card_pos.ne'
  exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h2)

end CFSG.RankThree.GroupTheory.SteinbergBM
