module

public import CFSG.Quasithin.Background.GoldschmidtD35CoreOff

public section

namespace CFSG.Quasithin.D35Core

open CFSG.QuasithinUnique.Setup.X3 CFSG.Quasithin Equiv
open scoped Matrix LinearAlgebra.Projectivization

variable {K : Type} [Field K] [Finite K] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) K)}
variable {pt : Fin 6 → ℙ K (Fin 3 → K)}

theorem arith_offender (m d : ℕ) (hm3 : m ≤ 3) (hd3 : d ≤ 3) (hle : 4 ^ d ≤ 16)
    (hbot : 64 ≤ 2 ^ m * 4 ^ d) : 4 ^ d = 16 ∧ 4 ≤ 2 ^ m := by
  interval_cases m <;> interval_cases d <;> omega

theorem card_offender (hval : IsValentiner K Γ) {E : Subgroup Γ} (hE : OffNat Γ E) {t₀ : Γ}
    (ht₀E : t₀ ∈ E) (ht₀1 : t₀ ≠ 1) : Nat.card (fixNat Γ E) = 16 ∧ 4 ≤ Nat.card E := by
  obtain ⟨hE1, -, hE2, hEoff⟩ := hE
  have hK := hval.1
  have hE2' : ∀ t ∈ E, t * t = 1 := fun t ht => by rw [← sq]; exact hE2 t ht
  have hΓ := card_valentiner hval
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpg : IsPGroup 2 E := fun g => ⟨1, Subtype.ext (by simpa using hE2 g.1 g.2)⟩
  obtain ⟨m, hm⟩ := hpg.exists_card_eq
  have hdvd : Nat.card E ∣ 1080 := hΓ ▸ Subgroup.card_subgroup_dvd_card E
  have hm3 : m ≤ 3 := by
    by_contra h
    push Not at h
    have h16 : 2 ^ 4 ∣ 1080 := by
      rw [hm] at hdvd
      exact (Nat.pow_dvd_pow 2 h).trans hdvd
    norm_num at h16
  obtain ⟨d, hd3, hd⟩ := exists_card_fixNat (Γ := Γ) E
  rw [hK] at hd
  have hle : Nat.card (fixNat Γ E) ≤ 16 := by
    have hsub := fixNat_subset (Γ := Γ) ht₀E
    have hc16 := card_fix_elt hval (hE2' t₀ ht₀E) ht₀1
    rw [Nat.card_coe_set_eq] at hc16 ⊢
    exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans hc16.le
  have hbot := hEoff ⊥ bot_le
  rw [Subgroup.card_bot, card_fixNat_bot hK, one_mul] at hbot
  rw [hd] at hle hbot ⊢
  rw [hm] at hbot ⊢
  exact arith_offender m d hm3 hd3 hle hbot

end CFSG.Quasithin.D35Core
