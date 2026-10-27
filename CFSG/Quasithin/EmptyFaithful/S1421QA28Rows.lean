module

public import CFSG.Quasithin.Vol2.Ch1EightFourInit
public import CFSG.LieType.Simplicity.Classical

public section

namespace CFSG.Quasithin

open CFSG.Blueprint CFSG.Quasithin.Ch1Four

namespace QA28

theorem two_pow_ne_three (t : ℕ) : 2 ^ t ≠ 3 := by
  rcases t with _ | t
  · norm_num
  · intro h
    have h2 : 2 ∣ 2 ^ (t + 1) := dvd_pow_self 2 (Nat.succ_ne_zero t)
    rw [h] at h2
    omega

theorem false_of_prime_mul {p : ℕ} (hp : p.Prime) (h : p * (p ^ 2 - 1) = 504) : False := by
  have hp10 : p < 11 := by
    by_contra hge
    push Not at hge
    have h1 : 11 * (11 ^ 2 - 1) ≤ p * (p ^ 2 - 1) :=
      Nat.mul_le_mul hge (Nat.sub_le_sub_right (Nat.pow_le_pow_left hge 2) 1)
    norm_num at h1
    omega
  interval_cases p <;> first | omega | (norm_num at hp)

theorem false_of_mul_sq {p : ℕ} (h : p * (p ^ 2 - 1) = 1008) : False := by
  have hp10 : p < 11 := by
    by_contra hge
    push Not at hge
    have h1 : 11 * (11 ^ 2 - 1) ≤ p * (p ^ 2 - 1) :=
      Nat.mul_le_mul hge (Nat.sub_le_sub_right (Nat.pow_le_pow_left hge 2) 1)
    norm_num at h1
    omega
  interval_cases p <;> omega

theorem card_isElemAbelianOfRank_two {p : ℕ} (hp : p.Prime) {V : Type} [Group V]
    (h : IsElemAbelianOfRank p 2 V) : Nat.card V = p ^ 2 := by
  obtain ⟨e⟩ := h
  have : NeZero p := ⟨hp.ne_zero⟩
  rw [Nat.card_congr e.toEquiv]
  change Nat.card (Fin 2 → ZMod p) = p ^ 2
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]

section Basic

variable {Q : Type} [Group Q] {B L : Subgroup Q}

theorem card_modO2 (h : IsPSL 2 2 3 (ModO2 B)) : Nat.card (ModO2 B) = 504 := by
  rw [(card_of_isPSL_two_two h).2]
  norm_num

theorem exists_two_pow_of_isExt [Finite Q] {PV PY : ∀ (V : Type) [Group V], Prop}
    (h : IsExt ↥B PV PY) (hV : ∀ (V : Type) [Group V], PV V → IsPGroup 2 V) {c : ℕ}
    (hY : ∀ (Y : Type) [Group Y], PY Y → Nat.card Y = c) :
    ∃ t : ℕ, c * 2 ^ t = Nat.card ↥B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨V, hVn, hPV, hPY⟩ := h
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup V
  obtain ⟨t, ht⟩ := IsPGroup.iff_card.mp (hV _ hPV)
  exact ⟨t, by rw [h1, hY _ hPY, ht]⟩

theorem false_of_isExt [Finite Q] (hB : Nat.card ↥B = 504) {PV PY : ∀ (V : Type) [Group V], Prop}
    (h : IsExt ↥B PV PY) (hV : ∀ (V : Type) [Group V], PV V → IsPGroup 2 V) {c : ℕ}
    (hY : ∀ (Y : Type) [Group Y], PY Y → Nat.card Y = c) (hc : ∀ t : ℕ, c * 2 ^ t ≠ 504) :
    False := by
  obtain ⟨t, ht⟩ := exists_two_pow_of_isExt h hV hY
  exact hc t (ht.trans hB)

theorem false_C3 (h28 : IsPSL 2 2 3 (ModO2 B)) (h : A312C3 B L) :
    False := by
  obtain ⟨f, hf, -⟩ := h
  exact not_three_dvd_card_of_isSz' hf (by rw [card_modO2 h28]; norm_num)

theorem false_C4 (h28 : IsPSL 2 2 3 (ModO2 B)) (h : A312C4 B L) : False := by
  have h1 := card_of_isPSL_three_two h.1
  have h2 := card_modO2 h28
  omega

theorem false_C5 (h28 : IsPSL 2 2 3 (ModO2 B)) (h : A312C5 B L) : False := by
  have h1 := card_of_isPSL_four_two h.1
  have h2 := card_modO2 h28
  omega

theorem false_C6 (hB : Nat.card ↥B = 504) (h : A312C6 B L) : False := by
  obtain ⟨hB' | hB', -⟩ := h
  · have := card_alt5 hB'
    omega
  · have := card_of_isPSL_three_two hB'
    omega

theorem false_C7 (hB : Nat.card ↥B = 504) (h : A312C7 B L) : False := by
  rcases h with ⟨hB', -⟩ | ⟨hB', -⟩
  · have := card_alt6 hB'
    omega
  · have := card_hat6 hB'
    omega

theorem false_C8 (hB : Nat.card ↥B = 504) (h : A312C8 B L) : False := by
  rcases h with ⟨p, hp, hp3, hB', -⟩ | ⟨hB', -⟩
  · have h2 := card_of_isPSL_two_odd hp (by omega) hB'
    exact false_of_mul_sq (p := p) (by omega)
  · have := card_alt5 hB'
    omega

theorem false_C9 (hB : Nat.card ↥B = 504) (h : A312C9 B L) : False := by
  rcases h with ⟨s, p, hp, hp3, hB', -⟩ | ⟨hB', -⟩ | ⟨hB', -⟩
  · have h2 := card_of_isSL2' hp hB'
    exact false_of_prime_mul hp (by omega)
  · have := card_alt6 hB'
    omega
  · have := card_hat6 hB'
    omega

theorem false_C10 (hB : Nat.card ↥B = 504) (h : A312C10 B L) : False := by
  obtain ⟨p, hp, hp3, ⟨V, hV, hVe, hY⟩, -⟩ := h
  have h1 := card_isElemAbelianOfRank_two hp hVe
  have h2 := card_of_isSL2' hp hY
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup V
  rw [h2, h1, hB] at h3
  have hp5 := five_le_of_prime hp hp3
  have h4 : 5 * (5 ^ 2 - 1) ≤ p * (p ^ 2 - 1) :=
    Nat.mul_le_mul hp5 (Nat.sub_le_sub_right (Nat.pow_le_pow_left hp5 2) 1)
  have h5 : 5 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hp5 2
  have h6 : 5 * (5 ^ 2 - 1) * 5 ^ 2 ≤ p * (p ^ 2 - 1) * p ^ 2 := Nat.mul_le_mul h4 h5
  norm_num at h6
  omega

theorem false_C11 (hB : Nat.card ↥B = 504) (h : A312C11 B L) : False := by
  have := card_alt6 h.1
  omega

theorem false_C12 [Finite Q] (hB : Nat.card ↥B = 504) (h : A312C12 B L) : False := by
  rcases h with ⟨hB' | hB', -⟩ | ⟨hB' | hB', -⟩
  · exact false_of_isExt hB hB' (fun V _ h => isPGroup_of_isE2 h)
      (fun Y _ h => card_alt5 h) (fun t => by omega)
  · exact false_of_isExt hB hB' (fun V _ h => isPGroup_of_isE2 h)
      (fun Y _ h => card_alt6 h) (fun t => by omega)
  · exact false_of_isExt hB hB' (fun V _ h => isPGroup_of_isE2 h)
      (fun Y _ h => card_alt5 h) (fun t => by omega)
  · exact false_of_isExt hB hB' (fun V _ h => isPGroup_of_isE2 h)
      (fun Y _ h => card_hat6 h) (fun t => by omega)

theorem false_C13 [Finite Q] (hB : Nat.card ↥B = 504)
    (h : A312C13 B L) : False := by
  obtain ⟨hB', -⟩ := h
  rcases hB' with hB' | hB' | hB' | hB' | hB' | hB' | hB'
  · have := card_of_isSporadic_M22' hB'
    omega
  · have := card_of_isPSL_three_four hB'
    omega
  · exact false_of_isExt hB hB' (fun V _ h => isPGroup_of_isE2 h)
      (fun Y _ h => card_alt7 h) (fun t => by omega)
  · exact false_of_isExt hB hB' (fun V _ h => isPGroup_of_isE2 h)
      (fun Y _ h => card_of_isPSL_three_two h) (fun t => by have := two_pow_ne_three t; omega)
  · exact false_of_isExt hB hB' (fun V _ h => isPGroup_of_isE2 h)
      (fun Y _ h => card_of_isPSL_three_two h) (fun t => by have := two_pow_ne_three t; omega)
  · exact false_of_isExt hB hB' (fun V _ h => isPGroup_of_isE2 h)
      (fun Y _ h => card_alt6 h) (fun t => by omega)
  · exact false_of_isExt hB hB' (fun V _ h => isPGroup_of_isE2 h)
      (fun Y _ h => card_alt5 h) (fun t => by omega)

theorem false_C14 [Finite Q] (hB : Nat.card ↥B = 504) (h : A312C14 B L) : False := by
  obtain ⟨hB' | hB' | hB' | hB', -⟩ := h
  · exact false_of_isExt hB hB' (fun V _ h => isPGroup_of_isE2 h)
      (fun Y _ h => card_of_isPSL_four_two h) (fun t => by omega)
  · exact false_of_isExt hB hB' (fun V _ h => isPGroup_of_isE2 h)
      (fun Y _ h => card_of_isPSL_three_two h) (fun t => by have := two_pow_ne_three t; omega)
  · exact false_of_isExt hB hB' (fun V _ h => isPGroup_of_isExtraspecial2 h)
      (fun Y _ h => card_of_isPSL_three_two h) (fun t => by have := two_pow_ne_three t; omega)
  · exact false_of_isExt hB hB' (fun V _ h => isPGroup_of_isE2 h)
      (fun Y _ h => card_hat6 h) (fun t => by omega)

theorem false_C15 (hB : Nat.card ↥B = 504) (h : A312C15 B L) : False := by
  have := card_alt5 h.1
  omega

theorem false_C16 [Finite Q] (hB : Nat.card ↥B = 504) (h : A312C16 B L) : False :=
  false_of_isExt hB h.1 (fun V _ h => isPGroup_of_isExtraspecial2 h)
    (fun Y _ h => card_alt5 h) (fun t => by omega)

theorem false_C17 [Finite Q]
    (h28 : IsPSL 2 2 3 (ModO2 B)) (hB : Nat.card ↥B = 504) (h : A312C17 B L) : False := by
  have h3 := card_modO2 h28
  obtain ⟨-, hB' | hB' | hB' | hB' | hB' | hB'⟩ := h
  · exact false_of_isExt hB hB' (fun V _ h => isPGroup_of_isExtraspecial2 h)
      (fun Y _ h => card_hatM22 h) (fun t => by omega)
  · exact false_of_isExt hB hB' (fun V _ h => isPGroup_of_isE2 h)
      (fun Y _ h => card_of_isSporadic_M24' h) (fun t => by omega)
  · have := card_alt5 hB'
    omega
  · have := card_hat6 hB'
    omega
  · have := card_of_isPSL_four_two hB'
    omega
  · have := card_of_isPSL_three_two hB'
    omega

theorem false_C18 [Finite Q] (hB : Nat.card ↥B = 504) (h : A312C18 B L) : False := by
  obtain ⟨hB' | hB', -⟩ := h
  · exact false_of_isExt hB hB' (fun V _ h => isPGroup_of_isZ4StarExtra2 h)
      (fun Y _ h => card_alt5 h) (fun t => by omega)
  · exact false_of_isExt hB hB' (fun V _ h => isPGroup_of_isZ4Cubed h)
      (fun Y _ h => card_of_isPSL_three_two h) (fun t => by have := two_pow_ne_three t; omega)

theorem false_C19 [Finite Q] (hB : Nat.card ↥B = 504) (h : A312C19 B L) : False := by
  obtain ⟨hB' | hB', -⟩ := h
  · exact false_of_isExt hB hB' (fun V _ h => isPGroup_of_isExtraspecial2 h)
      (fun Y _ h => card_of_isPSL_three_two h) (fun t => by have := two_pow_ne_three t; omega)
  · exact false_of_isExt hB hB' (fun V _ h => isPGroup_of_isE2 h)
      (fun Y _ h => card_hat6 h) (fun t => by omega)

theorem false_C20 (h28 : IsPSL 2 2 3 (ModO2 B)) (h : A312C20 B L) : False := by
  have h3 := card_modO2 h28
  obtain ⟨hB | hB, -⟩ := h
  · have := card_alt5 hB
    omega
  · have := card_of_isPSL_three_two hB
    omega

theorem rows_l28 [Finite Q]
    (h28 : IsPSL 2 2 3 (ModO2 B)) (hB : Nat.card ↥B = 504)
    (h : A312Case B L) : A312C2 B L := by
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact h
  · exact (false_C3 h28 h).elim
  · exact (false_C4 h28 h).elim
  · exact (false_C5 h28 h).elim
  · exact (false_C6 hB h).elim
  · exact (false_C7 hB h).elim
  · exact (false_C8 hB h).elim
  · exact (false_C9 hB h).elim
  · exact (false_C10 hB h).elim
  · exact (false_C11 hB h).elim
  · exact (false_C12 hB h).elim
  · exact (false_C13 hB h).elim
  · exact (false_C14 hB h).elim
  · exact (false_C15 hB h).elim
  · exact (false_C16 hB h).elim
  · exact (false_C17 h28 hB h).elim
  · exact (false_C18 hB h).elim
  · exact (false_C19 hB h).elim
  · exact (false_C20 h28 h).elim

theorem eq_bot_of_odd [Finite Q] (h28 : IsPSL 2 2 3 (ModO2 B)) {N : Subgroup ↥B} (hN : N.Normal)
    (hodd : Odd (Nat.card ↥N)) : N = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs : IsSimpleGroup (ModO2 B) :=
    (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 2 3 h28).2
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
    rw [card_modO2 h28] at hdvd
    obtain ⟨k, hk⟩ := hodd
    omega

theorem nonquasi_l28 [Finite Q] (h28 : IsPSL 2 2 3 (ModO2 B)) (hB : Nat.card ↥B = 504) (hBL : B ≤ L)
    (h : A312Nonquasi B L) : False := by
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
  have hVbot : V = ⊥ := eq_bot_of_odd h28 inferInstance hVodd
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
    exact false_of_prime_mul hp (by omega)
  · have hcard : Nat.card ↥B = 5 * (5 ^ 2 - 1) := by
      rw [← hBV, hφ]
      exact card_of_isSL2' (by norm_num) hSL
    norm_num at hcard
    omega

end Basic

end QA28

end CFSG.Quasithin
