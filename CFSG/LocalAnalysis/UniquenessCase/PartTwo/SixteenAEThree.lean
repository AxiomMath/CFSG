module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3RankLeTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16ae_exists_index_two_fix_ne_of_klein {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ x : W, x * x = 1) (hcard : Nat.card W = 2 ^ 6) {L : Subgroup (MulAut W)}
    (hL : IsPOnePlusTwo 3 ↥L) {X A : Subgroup (MulAut W)} (hAX : A ≤ X)
    (hAn : A ≤ Subgroup.normalizer (L : Set (MulAut W))) (hA : IsElemAbelian2 A)
    (hA4 : Nat.card A = 4) (hm : 1 < E3.mParam X) :
    ∃ B : Subgroup (MulAut W), B ≤ A ∧ E3.mQuot A B = 1 ∧ fixV B ≠ fixV A := by
  by_contra hcon
  have hall : ∀ B : Subgroup (MulAut W), B ≤ A → E3.mQuot A B = 1 → fixV B = fixV A := by
    intro B hBA hq
    by_contra hne
    exact hcon ⟨B, hBA, hq, hne⟩
  have hA1 : A ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hA4
    omega
  have hsup : (⨆ (t : MulAut W) (_ : t ∈ A ∧ t ≠ 1), fixV (Subgroup.zpowers t)) ≤ fixV A := by
    refine iSup₂_le ?_
    rintro t ⟨htA, ht1⟩
    refine (hall (Subgroup.zpowers t) (Subgroup.zpowers_le.2 htA) ?_).le
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have ht2 : orderOf t = 2 := orderOf_eq_prime (by simpa [pow_two] using hA.2 t htA) ht1
    have hzc : Nat.card ↥(Subgroup.zpowers t) = 2 := by rw [Nat.card_zpowers, ht2]
    have hrel : (Subgroup.zpowers t).relIndex A = 2 := by
      have h := Subgroup.relIndex_mul_card (Subgroup.zpowers t) A
      rw [inf_eq_left.2 (Subgroup.zpowers_le.2 htA), hzc, hA4] at h
      omega
    unfold E3.mQuot
    rw [hrel]
    exact padicValNat_self
  have hidx := s16c167_codim_core hW hcard hL hAn hA hA4
  have h2 : (fixV A).index ≤ 2 := (Subgroup.index_antitone hsup).trans hidx
  have h3 : rkIdx (fixV A) ≤ 1 := by
    unfold rkIdx
    have h0 : (fixV A).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h12 : (fixV A).index = 1 ∨ (fixV A).index = 2 := by omega
    rcases h12 with h | h
    · rw [h]; simp
    · rw [h]; exact padicValNat_self.le
  have h4 := E3.e3_2 hAX hA hA1
  omega

theorem s16ae_calABar_eq_empty_of_case168_3 (D : Data G) {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D ⊥ V L hV) (hm : 1 < mBar D.M ⊥ V hV)
    (h3 : Case168_3 D ⊥ V hV L) : calABar (mBar D.M ⊥ V hV) D.M ⊥ V hV = ∅ := by
  have hWsq : ∀ x : Vtil ⊥ V hV, x * x = 1 := s16c167_vtil_mul_self hV
  have hWcard : Nat.card (Vtil ⊥ V hV) = 2 ^ 6 := by
    have hp : IsPGroup 2 (Vtil ⊥ V hV) := by
      intro x
      refine ⟨1, ?_⟩
      simpa [pow_two] using hWsq x
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hp
    have h6 : rk ↥(⊤ : Subgroup (Vtil ⊥ V hV)) = 6 := h3.2.1
    unfold rk at h6
    rw [Subgroup.card_top, hn, padicValNat.prime_pow] at h6
    rw [hn, h6]
  have hnorm := s16c167_mbar_le_normalizer_lbar D hV hc h3
  rw [Set.eq_empty_iff_forall_notMem]
  intro A hAmem
  have h1 : mBar D.M ⊥ V hV ≤ E3.mQuot A ⊥ := E3.le_mQuot_bot_of_mem_aSet hAmem
  obtain ⟨hAX, hA1, hAel, hall⟩ := hAmem
  have h4 : Nat.card A ≤ 4 :=
    s16c167_card_le_four_of_le_normalizer_lbar hWsq hWcard h3.1 (hAX.trans hnorm) hAel
  have hpow : Nat.card A = 2 ^ rk ↥A :=
    card_eq_two_pow_of_isPGroup (E3.isPGroup_of_isElemAbelian2 hAel)
  have hmq : E3.mQuot A ⊥ = rk ↥A := by
    unfold E3.mQuot
    rw [Subgroup.relIndex_bot_left]
    rfl
  have hrk1 : 0 < rk ↥A := by
    rcases Nat.eq_zero_or_pos (rk ↥A) with h0 | h0
    · exfalso
      apply hA1
      rw [← Subgroup.card_eq_one]
      rw [hpow, h0, pow_zero]
    · exact h0
  by_cases hrk2 : rk ↥A = 2
  · have hA4 : Nat.card A = 4 := by rw [hpow, hrk2]; norm_num
    obtain ⟨B, hBA, hq, hne⟩ := s16ae_exists_index_two_fix_ne_of_klein hWsq hWcard h3.1 hAX
      (hAX.trans hnorm) hAel hA4 hm
    exact hne (hall B hBA (by omega))
  · have hle : rk ↥A ≤ 1 := by
      by_contra hgt
      have h3' : 3 ≤ rk ↥A := by omega
      have : 2 ^ 3 ≤ 2 ^ rk ↥A := Nat.pow_le_pow_right (by norm_num) h3'
      omega
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
