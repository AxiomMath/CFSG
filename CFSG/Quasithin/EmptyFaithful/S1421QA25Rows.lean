module

public import CFSG.Quasithin.Vol2.Ch1EightFourInit
public import CFSG.Quasithin.Background.B69Iso

public section

namespace CFSG.Quasithin

open CFSG.Blueprint CFSG.Quasithin.Ch1Four

namespace QA25

section Basic

variable {Q : Type} [Group Q] {B L : Subgroup Q}

theorem card_eq_pow [Finite Q] (h34 : IsPSL 3 2 2 (ModO2 B)) :
    ∃ j : ℕ, Nat.card ↥B = 20160 * 2 ^ j := by
  obtain ⟨j, hj⟩ := card_modO2_mul (H := ↥B)
  exact ⟨j, by rw [← hj, card_of_isPSL_three_four h34]⟩

theorem le_card [Finite Q] (h34 : IsPSL 3 2 2 (ModO2 B)) : 20160 ≤ Nat.card ↥B := by
  obtain ⟨j, hj⟩ := card_eq_pow h34
  have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  omega

theorem eq_bot_of_odd [Finite Q] (h34 : IsPSL 3 2 2 (ModO2 B)) {N : Subgroup ↥B} (hN : N.Normal)
    (hodd : Odd (Nat.card ↥N)) : N = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs : IsSimpleGroup (ModO2 B) := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 2 h34).2
  have hNn : (N.map (QuotientGroup.mk' (CFSG.pCore 2 ↥B))).Normal :=
    hN.map _ (QuotientGroup.mk'_surjective _)
  rcases hs.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' (CFSG.pCore 2 ↥B))) with h | h
  · have hle : N ≤ CFSG.pCore 2 ↥B := by
      have := (Subgroup.map_eq_bot_iff _).mp h
      rwa [QuotientGroup.ker_mk'] at this
    have hp : IsPGroup 2 ↥N := (CFSG.pCore_isPGroup (p := 2) (G := ↥B)).to_le hle
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
    have hk0 : k = 0 := by
      by_contra hk0
      rw [hk] at hodd
      exact (Nat.not_even_iff_odd.mpr hodd) ((Nat.even_pow' hk0).mpr even_two)
    rw [hk0, pow_zero] at hk
    exact Subgroup.eq_bot_of_card_eq _ hk
  · exfalso
    have hdvd : Nat.card (ModO2 B) ∣ Nat.card ↥N := by
      have h1 : Nat.card ↥(N.map (QuotientGroup.mk' (CFSG.pCore 2 ↥B))) ∣ Nat.card ↥N :=
        Subgroup.card_dvd_of_surjective
          (MonoidHom.subgroupMap_surjective (QuotientGroup.mk' (CFSG.pCore 2 ↥B)) N)
      rwa [h, Subgroup.card_top] at h1
    rw [card_of_isPSL_three_four h34] at hdvd
    obtain ⟨k, hk⟩ := hodd
    omega

theorem exists_two_pow_of_isExt [Finite Q] (h34 : IsPSL 3 2 2 (ModO2 B))
    {PV PY : ∀ (V : Type) [Group V], Prop} (h : IsExt ↥B PV PY)
    (hV : ∀ (V : Type) [Group V], PV V → IsPGroup 2 V) {c : ℕ}
    (hY : ∀ (Y : Type) [Group Y], PY Y → Nat.card Y = c) : ∃ t : ℕ, 20160 * 2 ^ t = c := by
  obtain ⟨V, hVn, hPV, hPY⟩ := h
  obtain ⟨t, ht⟩ := card_modO2_mul_of_le (V := V) (hV _ hPV)
  exact ⟨t, by rw [← card_of_isPSL_three_four h34, ht, hY _ hPY]⟩

theorem no_two_pow {t a m : ℕ} (hm : Odd m) (hm1 : m ≠ 1) (h : 2 ^ t = 2 ^ a * m) : False := by
  have := two_pow_mul_odd_inj (a := t) (b := a) (r := 1) (s := m) odd_one hm (by simpa using h)
  exact hm1 this.2.symm

theorem prime_dvd_20160 {p : ℕ} (hp : p.Prime) (h : p ∣ 20160) : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
  have e : (20160 : ℕ) = 2 ^ 6 * 3 ^ 2 * 5 * 7 := by norm_num
  rw [e] at h
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
          (hp.dvd_of_dvd_pow h)))
    · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp h)))
  · exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h)))

theorem odd_prime_mem [Finite Q] (h34 : IsPSL 3 2 2 (ModO2 B)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : p ∣ Nat.card ↥B) : p = 3 ∨ p = 5 ∨ p = 7 := by
  obtain ⟨j, hj⟩ := card_eq_pow h34
  rw [hj] at h
  have h1 : p ∣ 20160 := prime_dvd_of_dvd_mul_two_pow hp hp2 h
  rcases prime_dvd_20160 hp h1 with rfl | h | h | h
  · exact absurd rfl hp2
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)


theorem false_of_isPSL_two_two {Y : Type} [Group Y] {m : ℕ} (h : IsPSL 2 2 m Y)
    (hc : Nat.card Y = 20160) : False := by
  obtain ⟨hm2, hform⟩ := card_of_isPSL_two_two h
  rw [hc] at hform
  rcases Nat.lt_or_ge m 5 with hlt | hge
  · interval_cases m <;> omega
  · have h5 : 2 ^ 5 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hge
    have h4 : 4 ^ 5 ≤ 4 ^ m := Nat.pow_le_pow_right (by norm_num) hge
    have : 32 * 1023 ≤ 2 ^ m * (4 ^ m - 1) :=
      Nat.mul_le_mul (by simpa using h5) (by omega)
    omega

theorem false_of_isSz {Y : Type} [Group Y] {f : ℕ} (h : IsSz f Y)
    (hc : Nat.card Y = 20160) : False := by
  obtain ⟨-, a, ha, K, _, _, hf, hK, ⟨e⟩⟩ := h
  rw [hf] at hK
  rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK] at hc
  rcases Nat.lt_or_ge a 2 with hlt | hge
  · obtain rfl : a = 1 := by omega
    norm_num at hc
  · have h5 : 2 ^ 5 ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    generalize 2 ^ (2 * a + 1) = q at h5 hc
    have hq : 32 ≤ q := by simpa using h5
    have h1 : 32 * 32 ≤ q ^ 2 := by nlinarith
    have h2 : 31 ≤ q - 1 := by omega
    have h3 : 1025 ≤ q ^ 2 + 1 := by omega
    have h4 : 1024 * 31 * 1025 ≤ q ^ 2 * (q - 1) * (q ^ 2 + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
    omega

theorem false_of_isPSL_three_two_two_of_isPSL_four_two_one {Y : Type} [Group Y]
    (h3 : IsPSL 3 2 2 Y) (h4 : IsPSL 4 2 1 Y) : False := by
  obtain ⟨-, K3, _, _, hK3, ⟨e3⟩⟩ := h3
  obtain ⟨-, K4, _, _, hK4, ⟨e4⟩⟩ := h4
  exact B69.not_equiv_sl_four_psl_three (K := K4) (F := K3) (by rw [hK4]; norm_num)
    (by rw [hK3]; norm_num) e4 e3

theorem card_isElemAbelianOfRank_two {p : ℕ} (hp : p.Prime) {V : Type} [Group V]
    (h : IsElemAbelianOfRank p 2 V) : Nat.card V = p ^ 2 := by
  obtain ⟨e⟩ := h
  have : NeZero p := ⟨hp.ne_zero⟩
  rw [Nat.card_congr e.toEquiv]
  change Nat.card (Fin 2 → ZMod p) = p ^ 2
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]

theorem false_C2 (h34 : IsPSL 3 2 2 (ModO2 B)) (h : A312C2 B L) : False := by
  obtain ⟨⟨m, hm⟩, -⟩ := h
  exact false_of_isPSL_two_two hm (card_of_isPSL_three_four h34)

theorem false_C3 (h34 : IsPSL 3 2 2 (ModO2 B)) (h : A312C3 B L) :
    False := by
  obtain ⟨f, hf, -⟩ := h
  exact false_of_isSz hf (card_of_isPSL_three_four h34)

theorem false_C4 (h34 : IsPSL 3 2 2 (ModO2 B)) (h : A312C4 B L) : False := by
  have h1 := card_of_isPSL_three_two h.1
  have h2 := card_of_isPSL_three_four h34
  omega

theorem false_C5 (h34 : IsPSL 3 2 2 (ModO2 B)) (h : A312C5 B L) : False :=
  false_of_isPSL_three_two_two_of_isPSL_four_two_one h34 h.1

theorem false_C6 [Finite Q] (h34 : IsPSL 3 2 2 (ModO2 B)) (h : A312C6 B L) : False := by
  have hc := le_card h34
  obtain ⟨hB | hB, -⟩ := h
  · have := card_alt5 hB
    omega
  · have := card_of_isPSL_three_two hB
    omega

theorem false_C7 [Finite Q] (h34 : IsPSL 3 2 2 (ModO2 B)) (h : A312C7 B L) : False := by
  have hc := le_card h34
  rcases h with ⟨hB, -⟩ | ⟨hB, -⟩
  · have := card_alt6 hB
    omega
  · have := card_hat6 hB
    omega

theorem false_C8 [Finite Q] (h34 : IsPSL 3 2 2 (ModO2 B)) (h : A312C8 B L) : False := by
  have hc := le_card h34
  rcases h with ⟨p, hp, hp3, hB, -⟩ | ⟨hB, -⟩
  · have h2 := card_of_isPSL_two_odd hp (by omega) hB
    have hdvd : p ∣ Nat.card ↥B := by
      have : p ∣ 2 * Nat.card ↥B := by rw [h2]; exact dvd_mul_right p _
      rcases (Nat.Prime.dvd_mul hp).mp this with h | h
      · exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
      · exact h
    rcases odd_prime_mem h34 hp (by omega) hdvd with rfl | rfl | rfl
    · omega
    · norm_num at h2
      omega
    · norm_num at h2
      omega
  · have := card_alt5 hB
    omega

theorem false_C9 [Finite Q] (h34 : IsPSL 3 2 2 (ModO2 B)) (h : A312C9 B L) : False := by
  have hc := le_card h34
  rcases h with ⟨s, p, hp, hp3, hB, -⟩ | ⟨hB, -⟩ | ⟨hB, -⟩
  · have h2 := card_of_isSL2' hp hB
    have hdvd : p ∣ Nat.card ↥B := by rw [h2]; exact dvd_mul_right p _
    rcases odd_prime_mem h34 hp (by omega) hdvd with rfl | rfl | rfl
    · omega
    · norm_num at h2
      omega
    · norm_num at h2
      omega
  · have := card_alt6 hB
    omega
  · have := card_hat6 hB
    omega

theorem false_C10 [Finite Q] (h34 : IsPSL 3 2 2 (ModO2 B)) (h : A312C10 B L) : False := by
  have hc := le_card h34
  obtain ⟨p, hp, hp3, ⟨V, hV, hVe, hY⟩, -⟩ := h
  have h1 := card_isElemAbelianOfRank_two hp hVe
  have h2 := card_of_isSL2' hp hY
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup V
  rw [h2, h1] at h3
  have hdvd : p ∣ Nat.card ↥B := ⟨(p ^ 2 - 1) * p ^ 2, by rw [h3, mul_assoc]⟩
  rcases odd_prime_mem h34 hp (by omega) hdvd with rfl | rfl | rfl
  · omega
  · norm_num at h3
    omega
  · norm_num at h3
    omega

theorem false_C11 [Finite Q] (h34 : IsPSL 3 2 2 (ModO2 B)) (h : A312C11 B L) : False := by
  have hc := le_card h34
  have := card_alt6 h.1
  omega


theorem false_of_isExt_small [Finite Q] (h34 : IsPSL 3 2 2 (ModO2 B))
    {PV PY : ∀ (V : Type) [Group V], Prop} (h : IsExt ↥B PV PY)
    (hV : ∀ (V : Type) [Group V], PV V → IsPGroup 2 V) {c : ℕ}
    (hY : ∀ (Y : Type) [Group Y], PY Y → Nat.card Y = c) (hc : c < 20160) : False := by
  obtain ⟨t, ht⟩ := exists_two_pow_of_isExt h34 h hV hY
  have : 1 ≤ 2 ^ t := Nat.one_le_two_pow
  omega

theorem false_C12 [Finite Q] (h34 : IsPSL 3 2 2 (ModO2 B)) (h : A312C12 B L) : False := by
  rcases h with ⟨hB | hB, -⟩ | ⟨hB | hB, -⟩
  · exact false_of_isExt_small h34 hB (fun V _ h => isPGroup_of_isE2 h)
      (fun Y _ h => card_alt5 h) (by norm_num)
  · exact false_of_isExt_small h34 hB (fun V _ h => isPGroup_of_isE2 h)
      (fun Y _ h => card_alt6 h) (by norm_num)
  · exact false_of_isExt_small h34 hB (fun V _ h => isPGroup_of_isE2 h)
      (fun Y _ h => card_alt5 h) (by norm_num)
  · exact false_of_isExt_small h34 hB (fun V _ h => isPGroup_of_isE2 h)
      (fun Y _ h => card_hat6 h) (by norm_num)

theorem of_C13 [Finite Q] (h34 : IsPSL 3 2 2 (ModO2 B))
    (h : A312C13 B L) : IsPSL 3 2 2 ↥B ∧ IsSporadic .M23 ↥L := by
  obtain ⟨hB, hL⟩ := h
  refine ⟨?_, hL⟩
  rcases hB with hB | hB | hB | hB | hB | hB | hB
  · exfalso
    have h1 := card_of_isSporadic_M22' hB
    obtain ⟨j, hj⟩ := card_eq_pow h34
    rw [h1] at hj
    have : 2 ^ j = 2 ^ 1 * 11 := by omega
    exact no_two_pow (a := 1) (m := 11) (by decide) (by norm_num) this
  · exact hB
  · exact (false_of_isExt_small h34 hB (fun V _ h => isPGroup_of_isE2 h)
      (fun Y _ h => card_alt7 h) (by norm_num)).elim
  · exact (false_of_isExt_small h34 hB (fun V _ h => isPGroup_of_isE2 h)
      (fun Y _ h => card_of_isPSL_three_two h) (by norm_num)).elim
  · exact (false_of_isExt_small h34 hB (fun V _ h => isPGroup_of_isE2 h)
      (fun Y _ h => card_of_isPSL_three_two h) (by norm_num)).elim
  · exact (false_of_isExt_small h34 hB (fun V _ h => isPGroup_of_isE2 h)
      (fun Y _ h => card_alt6 h) (by norm_num)).elim
  · exact (false_of_isExt_small h34 hB (fun V _ h => isPGroup_of_isE2 h)
      (fun Y _ h => card_alt5 h) (by norm_num)).elim

theorem false_C14 [Finite Q] (h34 : IsPSL 3 2 2 (ModO2 B)) (h : A312C14 B L) : False := by
  obtain ⟨hB | hB | hB | hB, -⟩ := h
  · obtain ⟨V, hVn, hV, hY⟩ := hB
    have hV2 : IsPGroup 2 ↥V := isPGroup_of_isE2 hV
    obtain ⟨t, ht⟩ := card_modO2_mul_of_le (V := V) hV2
    have hc4 := card_of_isPSL_four_two hY
    rw [card_of_isPSL_three_four h34, hc4] at ht
    have ht0 : t = 0 := by
      have : 2 ^ t = 1 := by omega
      exact (Nat.pow_eq_one.mp this).resolve_left (by norm_num)
    subst ht0
    have hle : V ≤ CFSG.pCore 2 ↥B := le_sSup ⟨hVn, hV2⟩
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup V
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥B)
    rw [hc4] at h1
    rw [card_of_isPSL_three_four h34] at h2
    have hcard : Nat.card ↥(CFSG.pCore 2 ↥B) ≤ Nat.card ↥V := by
      have : Nat.card ↥(CFSG.pCore 2 ↥B) * 20160 = Nat.card ↥V * 20160 := by omega
      exact (Nat.eq_of_mul_eq_mul_right (by norm_num) this).le
    have hVeq : V = CFSG.pCore 2 ↥B := Subgroup.eq_of_le_of_card_ge hle hcard
    have hN : (CFSG.pCore 2 ↥B).Normal := CFSG.pCore_normal
    exact false_of_isPSL_three_two_two_of_isPSL_four_two_one h34
      (CFSG.SectionRank.statedClassicalModel_of_mulEquiv
        (QuotientGroup.quotientMulEquivOfEq hVeq.symm) hY)
  · exact false_of_isExt_small h34 hB (fun V _ h => isPGroup_of_isE2 h)
      (fun Y _ h => card_of_isPSL_three_two h) (by norm_num)
  · exact false_of_isExt_small h34 hB (fun V _ h => isPGroup_of_isExtraspecial2 h)
      (fun Y _ h => card_of_isPSL_three_two h) (by norm_num)
  · exact false_of_isExt_small h34 hB (fun V _ h => isPGroup_of_isE2 h)
      (fun Y _ h => card_hat6 h) (by norm_num)

theorem false_C15 [Finite Q] (h34 : IsPSL 3 2 2 (ModO2 B)) (h : A312C15 B L) : False := by
  have hc := le_card h34
  have := card_alt5 h.1
  omega

theorem false_C16 [Finite Q] (h34 : IsPSL 3 2 2 (ModO2 B)) (h : A312C16 B L) : False :=
  false_of_isExt_small h34 h.1 (fun V _ h => isPGroup_of_isExtraspecial2 h)
    (fun Y _ h => card_alt5 h) (by norm_num)

theorem false_C17 [Finite Q]
    (h34 : IsPSL 3 2 2 (ModO2 B)) (h : A312C17 B L) : False := by
  have h3 := card_of_isPSL_three_four h34
  obtain ⟨-, hB | hB | hB | hB | hB | hB⟩ := h
  · obtain ⟨t, ht⟩ := exists_two_pow_of_isExt h34 hB (fun V _ h => isPGroup_of_isExtraspecial2 h)
      (fun Y _ h => card_hatM22 h)
    have : 2 ^ t = 2 ^ 1 * 33 := by omega
    exact no_two_pow (a := 1) (m := 33) (by decide) (by norm_num) this
  · obtain ⟨t, ht⟩ := exists_two_pow_of_isExt h34 hB (fun V _ h => isPGroup_of_isE2 h)
      (fun Y _ h => card_of_isSporadic_M24' h)
    have : 2 ^ t = 2 ^ 4 * 759 := by omega
    exact no_two_pow (a := 4) (m := 759) (by decide) (by norm_num) this
  · have := card_alt5 hB
    omega
  · have := card_hat6 hB
    omega
  · exact false_of_isPSL_three_two_two_of_isPSL_four_two_one h34 hB
  · have := card_of_isPSL_three_two hB
    omega

theorem false_C18 [Finite Q] (h34 : IsPSL 3 2 2 (ModO2 B)) (h : A312C18 B L) : False := by
  obtain ⟨hB | hB, -⟩ := h
  · exact false_of_isExt_small h34 hB (fun V _ h => isPGroup_of_isZ4StarExtra2 h)
      (fun Y _ h => card_alt5 h) (by norm_num)
  · exact false_of_isExt_small h34 hB (fun V _ h => isPGroup_of_isZ4Cubed h)
      (fun Y _ h => card_of_isPSL_three_two h) (by norm_num)

theorem false_C19 [Finite Q] (h34 : IsPSL 3 2 2 (ModO2 B)) (h : A312C19 B L) : False := by
  obtain ⟨hB | hB, -⟩ := h
  · exact false_of_isExt_small h34 hB (fun V _ h => isPGroup_of_isExtraspecial2 h)
      (fun Y _ h => card_of_isPSL_three_two h) (by norm_num)
  · exact false_of_isExt_small h34 hB (fun V _ h => isPGroup_of_isE2 h)
      (fun Y _ h => card_hat6 h) (by norm_num)

theorem false_C20 (h34 : IsPSL 3 2 2 (ModO2 B)) (h : A312C20 B L) : False := by
  have h3 := card_of_isPSL_three_four h34
  obtain ⟨hB | hB, -⟩ := h
  · have := card_alt5 hB
    omega
  · have := card_of_isPSL_three_two hB
    omega

theorem rows_l34 [Finite Q]
    (h34 : IsPSL 3 2 2 (ModO2 B)) (h : A312Case B L) :
    IsPSL 3 2 2 ↥B ∧ IsSporadic .M23 ↥L := by
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact (false_C2 h34 h).elim
  · exact (false_C3 h34 h).elim
  · exact (false_C4 h34 h).elim
  · exact (false_C5 h34 h).elim
  · exact (false_C6 h34 h).elim
  · exact (false_C7 h34 h).elim
  · exact (false_C8 h34 h).elim
  · exact (false_C9 h34 h).elim
  · exact (false_C10 h34 h).elim
  · exact (false_C11 h34 h).elim
  · exact (false_C12 h34 h).elim
  · exact of_C13 h34 h
  · exact (false_C14 h34 h).elim
  · exact (false_C15 h34 h).elim
  · exact (false_C16 h34 h).elim
  · exact (false_C17 h34 h).elim
  · exact (false_C18 h34 h).elim
  · exact (false_C19 h34 h).elim
  · exact (false_C20 h34 h).elim


theorem nonquasi_l34 [Finite Q] (h34 : IsPSL 3 2 2 (ModO2 B)) (hBL : B ≤ L)
    (h : A312Nonquasi B L) : False := by
  have hc := le_card h34
  set OL : Subgroup Q := (CFSG.oddCore ↥L).map L.subtype with hOL
  have hsub : OL.subgroupOf L = CFSG.oddCore ↥L :=
    Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
  have hLO : L ≤ Subgroup.normalizer (OL : Set Q) := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp ?_
    rw [hsub]
    infer_instance
  have hBO : B ≤ Subgroup.normalizer (OL : Set Q) := hBL.trans hLO
  have : (OL.subgroupOf B).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hBO
  set V := OL.subgroupOf B with hV
  have hVodd : Odd (Nat.card V) := by
    have h1 : Nat.card V = Nat.card ↥(OL ⊓ B) := by
      rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective B.subtype_injective]
    have h2 : Nat.card ↥(OL ⊓ B) ∣ Nat.card OL := Subgroup.card_dvd_of_le inf_le_left
    have h3 : Nat.card OL = Nat.card (CFSG.oddCore ↥L) :=
      Subgroup.card_map_of_injective L.subtype_injective
    rw [h1]
    exact (h3 ▸ A312.odd_card_oddCore ↥L).of_dvd_nat h2
  have hVbot : V = ⊥ := eq_bot_of_odd h34 inferInstance hVodd
  have : (OL.subgroupOf (B ⊔ OL)).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hBO
  have hφ : Nat.card (↥B ⧸ V) = (OL.subgroupOf (B ⊔ OL)).index :=
    Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient B OL hBO).toEquiv
  have hBV : Nat.card (↥B ⧸ V) = Nat.card ↥B := by
    rw [hVbot]
    exact Nat.card_congr QuotientGroup.quotientBot.toEquiv
  unfold A312Nonquasi at h
  dsimp only at h
  rcases h with ⟨-, hLB, p, hp, hp2, hSL⟩ | ⟨-, -, N, hN, rfl, hSL⟩
  · have hcard : Nat.card ↥B = p * (p ^ 2 - 1) := by
      rw [← hBV, hφ, ← hLB, hsub]
      exact card_of_isSL2' hp hSL
    have hdvd : p ∣ Nat.card ↥B := by rw [hcard]; exact dvd_mul_right p _
    rcases odd_prime_mem h34 hp hp2 hdvd with rfl | rfl | rfl <;> norm_num at hcard <;> omega
  · have hcard : Nat.card ↥B = 5 * (5 ^ 2 - 1) := by
      rw [← hBV, hφ]
      exact card_of_isSL2' (by norm_num) hSL
    norm_num at hcard
    omega

end Basic

end QA25


end CFSG.Quasithin
