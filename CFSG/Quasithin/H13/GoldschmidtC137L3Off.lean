module

public import CFSG.Quasithin.Background.StabSubBasics
public import CFSG.Quasithin.H13.GoldschmidtC137L3Fix
public import CFSG.Quasithin.Background.B1Basic

public section

namespace CFSG.Quasithin.H13.U3.GC137

open CFSG.Quasithin CFSG.Quasithin.L3

variable {M : Type} [CommGroup M] [Finite M] (φ : M ≃* Multiplicative Vec) {u : M} (hu : u ≠ 1)

include φ

omit [Finite M] in
theorem card_M : Nat.card M = 8 := by
  rw [Nat.card_congr (crdEquiv φ), Nat.card_eq_fintype_card]
  simp

omit [Finite M] in
theorem rkIdx_of_card {H : Subgroup M} {k : ℕ} (hH : Nat.card H = 2 ^ k) (hk : k ≤ 3) :
    rkIdx H = 3 - k := by
  have h1 := Subgroup.card_mul_index H
  rw [card_M φ, hH] at h1
  have h2 : H.index = 2 ^ (3 - k) := by
    have h3 : (8 : ℕ) = 2 ^ k * 2 ^ (3 - k) := by
      rw [← pow_add]
      have : k + (3 - k) = 3 := by omega
      rw [this]
      norm_num
    rw [h3] at h1
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
  unfold rkIdx
  rw [h2, padicValNat.prime_pow]

omit φ [Finite M] in
theorem rk_of_card {A : Subgroup (MulAut M)} {k : ℕ} (hA : Nat.card A = 2 ^ k) : rk A = k := by
  unfold rk
  rw [hA, padicValNat.prime_pow]

omit φ [Finite M] in
theorem card_zpowers_invol {t : MulAut M} (h2 : t ^ 2 = 1) (h1 : t ≠ 1) :
    Nat.card (Subgroup.zpowers t) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime h2 h1

theorem subgroup_le_v4M_cases {B : Subgroup (MulAut M)} (hB : B ≤ v4M φ u hu) :
    B = ⊥ ∨ (∃ t ∈ v4M φ u hu, t ≠ 1 ∧ B = Subgroup.zpowers t) ∨ B = v4M φ u hu := by
  have hdvd : Nat.card B ∣ 4 := by
    rw [← card_v4M φ hu]
    exact Subgroup.card_dvd_of_le hB
  obtain ⟨k, hk, hkB⟩ :=
    (Nat.dvd_prime_pow Nat.prime_two).1 (show Nat.card B ∣ 2 ^ 2 by simpa using hdvd)
  interval_cases k
  · left
    exact Subgroup.eq_bot_of_card_eq B (by simpa using hkB)
  · right; left
    have h1 : 1 < Nat.card B := by rw [hkB]; norm_num
    obtain ⟨t, ht⟩ :=
      (Subgroup.ne_bot_iff_exists_ne_one).1 ((Subgroup.one_lt_card_iff_ne_bot _).1 h1)
    have ht1 : (t : MulAut M) ≠ 1 := fun h => ht (Subtype.ext h)
    have htv : (t : MulAut M) ∈ v4M φ u hu := hB t.2
    refine ⟨t, htv, ht1, ?_⟩
    symm
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 t.2)
    rw [card_zpowers_invol (v4M_sq φ htv) ht1, hkB]
    norm_num
  · right; right
    exact Subgroup.eq_of_le_of_card_ge hB (by rw [card_v4M φ hu, hkB]; norm_num)

theorem rAV_eq_one {A : Subgroup (MulAut M)} (hA : A ≤ v4M φ u hu) (hA1 : A ≠ ⊥) : rAV A = 1 := by
  have key : rkIdx (fixV A) = rk A := by
    rcases subgroup_le_v4M_cases φ hu hA with h | ⟨t, htv, ht1, h⟩ | h
    · exact absurd h hA1
    · have h2 := v4M_sq φ htv
      rw [h, rkIdx_of_card φ (k := 2)
          (by rw [card_fixV_zpowers_invol φ h2 ht1]; norm_num) (by norm_num),
        rk_of_card (k := 1) (by rw [card_zpowers_invol h2 ht1]; norm_num)]
    · rw [h, rkIdx_of_card φ (k := 1) (by rw [card_fixV_v4M φ hu]; norm_num) (by norm_num),
        rk_of_card (k := 2) (by rw [card_v4M φ hu]; norm_num)]
  have hrk : (rk A : ℚ) ≠ 0 := by
    have : 0 < rk A := by
      rw [← key]
      rcases subgroup_le_v4M_cases φ hu hA with h | ⟨t, htv, ht1, h⟩ | h
      · exact absurd h hA1
      · have h2 := v4M_sq φ htv
        rw [h, rkIdx_of_card φ (k := 2)
          (by rw [card_fixV_zpowers_invol φ h2 ht1]; norm_num) (by norm_num)]
        norm_num
      · rw [h, rkIdx_of_card φ (k := 1) (by rw [card_fixV_v4M φ hu]; norm_num) (by norm_num)]
        norm_num
    exact_mod_cast this.ne'
  unfold rAV
  rw [key]
  exact div_self hrk

theorem not_strong_of_le_v4M {B : Subgroup (MulAut M)}
    (hB : IsFFStarOffender (v4M φ u hu) B) : ¬ rAV B < 1 := by
  have := rAV_eq_one φ hu hB.1 hB.2.1
  rw [this]
  exact lt_irrefl _

omit φ [Finite M] in
theorem isElemAbelian2_zpowers_gc {s : MulAut M} (hs : s ^ 2 = 1) :
    IsElemAbelian2 (Subgroup.zpowers s) :=
  CFSG.Quasithin.StabLat.isElemAbelian2_zpowers hs

omit φ [Finite M] in
theorem conjAut_zpowers (g t : MulAut M) :
    B1.conjAut g (Subgroup.zpowers t) = Subgroup.zpowers (g * t * g⁻¹) := by
  ext x
  rw [B1.mem_conjAut, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [conj_zpow, hk]
    group
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [← hk, conj_zpow]
    group

theorem isFFStarOffender_zpowers {t : MulAut M} (htv : t ∈ v4M φ u hu) (ht1 : t ≠ 1) :
    IsFFStarOffender (v4M φ u hu) (Subgroup.zpowers t) := by
  have h2 := v4M_sq φ htv
  have hc : Nat.card (Subgroup.zpowers t) = 2 := card_zpowers_invol h2 ht1
  refine ⟨Subgroup.zpowers_le.2 htv, fun hb => ht1 (Subgroup.zpowers_eq_bot.1 hb),
    isElemAbelian2_zpowers_gc h2, ?_⟩
  intro B hB
  have hdvd : Nat.card B ∣ 2 := by
    rw [← hc]
    exact Subgroup.card_dvd_of_le hB
  rw [card_fixV_zpowers_invol φ h2 ht1, hc]
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
  · rw [Subgroup.eq_bot_of_card_eq B h, B1.fixV_bot, Subgroup.card_bot]
    rw [Subgroup.card_top, card_M φ]
  · have : B = Subgroup.zpowers t :=
      Subgroup.eq_of_le_of_card_ge hB (by rw [hc, h])
    rw [this, card_fixV_zpowers_invol φ h2 ht1, hc]

theorem offender_cover {A : Subgroup (MulAut M)} (hA : IsFFStarOffender (v4M φ u hu) A) :
    ∃ (r : ℕ) (Ai : Fin r → Subgroup (MulAut M)), A = ⨆ k, Ai k ∧
      ∀ k, IsFFStarOffender (v4M φ u hu) (Ai k) ∧
        ∃ t ∈ v4M φ u hu, t ≠ 1 ∧ Ai k = Subgroup.zpowers t := by
  rcases subgroup_le_v4M_cases φ hu hA.1 with h | ⟨t, htv, ht1, h⟩ | h
  · exact absurd h hA.2.1
  · exact ⟨1, fun _ => A, (iSup_const).symm, fun _ => ⟨hA, t, htv, ht1, h⟩⟩
  · obtain ⟨t₁, ht₁v, ht₁1⟩ : ∃ t ∈ v4M φ u hu, t ≠ 1 := by
      obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1
        ((Subgroup.one_lt_card_iff_ne_bot _).1 (by rw [card_v4M φ hu]; norm_num) :
          v4M φ u hu ≠ ⊥)
      exact ⟨a, a.2, fun h' => ha (Subtype.ext h')⟩
    have ht₁2 := v4M_sq φ ht₁v
    have hc₁ := card_zpowers_invol ht₁2 ht₁1
    have hlt : Subgroup.zpowers t₁ < v4M φ u hu := by
      refine lt_of_le_of_ne (Subgroup.zpowers_le.2 ht₁v) fun heq => ?_
      have h1 := hc₁
      rw [heq, card_v4M φ hu] at h1
      omega
    obtain ⟨t₂, ht₂v, ht₂n⟩ := Set.exists_of_ssubset (SetLike.coe_ssubset_coe.2 hlt)
    have ht₂1 : t₂ ≠ 1 := fun h' => ht₂n (h' ▸ Subgroup.one_mem _)
    have hjoin : Subgroup.zpowers t₁ ⊔ Subgroup.zpowers t₂ = v4M φ u hu := by
      set J := Subgroup.zpowers t₁ ⊔ Subgroup.zpowers t₂ with hJ
      have hJle : J ≤ v4M φ u hu :=
        sup_le (Subgroup.zpowers_le.2 ht₁v) (Subgroup.zpowers_le.2 ht₂v)
      have hd4 : Nat.card J ∣ 4 := by
        rw [← card_v4M φ hu]
        exact Subgroup.card_dvd_of_le hJle
      have hd2 : 2 ∣ Nat.card J := by
        rw [← hc₁]
        exact Subgroup.card_dvd_of_le le_sup_left
      have hne : Nat.card J ≠ 2 := fun h2 => by
        have hEq : Subgroup.zpowers t₁ = J :=
          Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h2, hc₁])
        exact ht₂n (hEq ▸ ((le_sup_right : Subgroup.zpowers t₂ ≤ J) (Subgroup.mem_zpowers t₂)))
      have h4 : Nat.card J = 4 := by
        have hle := Nat.le_of_dvd (by norm_num) hd4
        have hp := Nat.card_pos (α := J)
        interval_cases hk : Nat.card J <;> omega
      exact Subgroup.eq_of_le_of_card_ge hJle (by rw [h4, card_v4M φ hu])
    refine ⟨2, ![Subgroup.zpowers t₁, Subgroup.zpowers t₂], ?_, ?_⟩
    · rw [h, ← hjoin]
      refine le_antisymm
        (sup_le (le_iSup (fun k => ![Subgroup.zpowers t₁, Subgroup.zpowers t₂] k) 0)
          (le_iSup (fun k => ![Subgroup.zpowers t₁, Subgroup.zpowers t₂] k) 1)) ?_
      refine iSup_le fun k => ?_
      fin_cases k
      · exact le_sup_left
      · exact le_sup_right
    · intro k
      fin_cases k
      · exact ⟨isFFStarOffender_zpowers φ hu ht₁v ht₁1, t₁, ht₁v, ht₁1, rfl⟩
      · exact ⟨isFFStarOffender_zpowers φ hu ht₂v ht₂1, t₂, ht₂v, ht₂1, rfl⟩

end CFSG.Quasithin.H13.U3.GC137
