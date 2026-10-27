module

public import CFSG.Quasithin.Vol2.Ch1EightFourInit
public import CFSG.Quasithin.Background.B69Iso

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Quasithin CFSG.Quasithin.Ch1Four CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem prime_dvd_20160 {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : p ∣ 20160 * 2 ^ k) :
    p = 3 ∨ p = 5 ∨ p = 7 := by
  have hcop : Nat.Coprime p (2 ^ k) :=
    ((Nat.coprime_primes hp Nat.prime_two).mpr hp2).pow_right k
  have h1 : p ∣ 2 ^ 6 * 3 ^ 2 * 5 * 7 := by
    have := hcop.dvd_of_dvd_mul_right h
    norm_num at this ⊢
    exact this
  rcases (Nat.Prime.dvd_mul hp).mp h1 with h3 | h7
  · rcases (Nat.Prime.dvd_mul hp).mp h3 with h4 | h5
    · rcases (Nat.Prime.dvd_mul hp).mp h4 with h6 | h9
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h6)) hp2
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h9))
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h5))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h7))

theorem false_of_eq_psl2 {p j : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (h : 20160 * 2 ^ j = p * (p ^ 2 - 1)) : False := by
  have hdvd : p ∣ 20160 * 2 ^ j := h ▸ dvd_mul_right p _
  have h1 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  rcases prime_dvd_20160 hp (by omega) hdvd with rfl | rfl | rfl
  · omega
  · norm_num at h
    omega
  · norm_num at h
    omega

theorem false_of_dvd_of_not_dvd {t c p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpc : p ∣ c)
    (hp' : ¬ p ∣ 20160) (h : 20160 * 2 ^ t = c) : False := by
  subst h
  have hcop : Nat.Coprime p (2 ^ t) :=
    ((Nat.coprime_primes hp Nat.prime_two).mpr hp2).pow_right t
  exact hp' (hcop.dvd_of_dvd_mul_right hpc)

theorem false_of_lt {t c : ℕ} (hc : c < 20160) (h : 20160 * 2 ^ t = c) : False := by
  have h1 : 1 ≤ 2 ^ t := Nat.one_le_two_pow
  generalize 2 ^ t = x at h h1
  omega

theorem psl22_ne_20160 (n : ℕ) : 2 ^ n * (4 ^ n - 1) ≠ 20160 := by
  intro h
  rcases Nat.lt_or_ge n 7 with hlt | hge
  · interval_cases n <;> omega
  · have h1 : 2 ^ 7 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hge
    have h2 : 4 ^ 7 ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) hge
    have h3 : 2 ^ 7 * (4 ^ 7 - 1) ≤ 2 ^ n * (4 ^ n - 1) :=
      Nat.mul_le_mul h1 (Nat.sub_le_sub_right h2 1)
    norm_num at h3
    omega

theorem false_of_isPSL_three_four_of_isPSL_four_two {X : Type} [Group X] (h3 : IsPSL 3 2 2 X)
    (h4 : IsPSL 4 2 1 X) : False := by
  obtain ⟨-, K3, _, _, hK3, ⟨e3⟩⟩ := h3
  obtain ⟨-, K4, _, _, hK4, ⟨e4⟩⟩ := h4
  exact B69.not_equiv_sl_four_psl_three (K := K4) (F := K3) (by rw [hK4]; norm_num)
    (by rw [hK3]; norm_num) e4 e3

variable {Q : Type} [Group Q] [Finite Q]

structure ModL34 (B : Subgroup Q) : Prop where
  psl : IsPSL 3 2 2 (ModO2 B)

variable {B L : Subgroup Q}

omit [Finite Q] in
theorem ModL34.card (h : ModL34 B) : Nat.card (ModO2 B) = 20160 :=
  card_of_isPSL_three_four h.psl

omit [Finite Q] in
theorem ModL34.simple (h : ModL34 B) : IsSimpleGroup (ModO2 B) :=
  (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 2 h.psl).2

theorem ModL34.exists_card (h : ModL34 B) : ∃ j, 20160 * 2 ^ j = Nat.card ↥B := by
  obtain ⟨j, hj⟩ := card_modO2_mul (H := ↥B)
  rw [h.card] at hj
  exact ⟨j, hj⟩

theorem ModL34.exists_card_quot (h : ModL34 B) {V : Subgroup ↥B} [V.Normal]
    (hV : IsPGroup 2 V) : ∃ t, 20160 * 2 ^ t = Nat.card (↥B ⧸ V) := by
  obtain ⟨t, ht⟩ := card_modO2_mul_of_le hV
  rw [h.card] at ht
  exact ⟨t, ht⟩

theorem ModL34.false_of_card (h : ModL34 B) {c : ℕ} (hc : c < 20160) (hB : Nat.card ↥B = c) :
    False := by
  obtain ⟨j, hj⟩ := h.exists_card
  exact false_of_lt hc (hj.trans hB)

theorem ModL34.false_of_ext {PV PY : ∀ (V : Type) [Group V], Prop} (h : ModL34 B)
    (hE : IsExt ↥B PV PY) (hV : ∀ (V : Type) [Group V], PV V → IsPGroup 2 V) {c : ℕ}
    (hc : c < 20160) (hY : ∀ (Y : Type) [Group Y], PY Y → Nat.card Y = c) : False := by
  obtain ⟨V, hVn, hPV, hPY⟩ := hE
  obtain ⟨t, ht⟩ := h.exists_card_quot (hV _ hPV)
  exact false_of_lt hc (ht.trans (hY _ hPY))

theorem ModL34.false_of_ext_eleven {PV PY : ∀ (V : Type) [Group V], Prop} (h : ModL34 B)
    (hE : IsExt ↥B PV PY) (hV : ∀ (V : Type) [Group V], PV V → IsPGroup 2 V) {c : ℕ}
    (hc : 11 ∣ c) (hY : ∀ (Y : Type) [Group Y], PY Y → Nat.card Y = c) : False := by
  obtain ⟨V, hVn, hPV, hPY⟩ := hE
  obtain ⟨t, ht⟩ := h.exists_card_quot (hV _ hPV)
  exact false_of_dvd_of_not_dvd (by norm_num) (by norm_num) hc (by norm_num)
    (ht.trans (hY _ hPY))

omit [Finite Q] in
theorem ModL34.false_of_modO2_L42 (h : ModL34 B) (h4 : IsPSL 4 2 1 (ModO2 B)) : False :=
  false_of_isPSL_three_four_of_isPSL_four_two h.psl h4

theorem ModL34.false_of_ext_L42 {PV : ∀ (V : Type) [Group V], Prop} (h : ModL34 B)
    (hE : IsExt ↥B PV (fun Y _ => IsPSL 4 2 1 Y))
    (hV : ∀ (V : Type) [Group V], PV V → IsPGroup 2 V) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨V, hVn, hPV, hPY⟩ := hE
  have hV2 : IsPGroup 2 ↥V := hV _ hPV
  have hle : V ≤ CFSG.pCore 2 ↥B := le_sSup ⟨hVn, hV2⟩
  have hcV : Nat.card (↥B ⧸ V) = Nat.card (ModO2 B) := by
    rw [h.card, card_of_isPSL_four_two hPY]
  have hcard : Nat.card ↥(CFSG.pCore 2 ↥B) ≤ Nat.card ↥V := by
    have h1 := V.card_eq_card_quotient_mul_card_subgroup
    have h2 := (CFSG.pCore 2 ↥B).card_eq_card_quotient_mul_card_subgroup
    rw [hcV] at h1
    have hpos : 0 < Nat.card (ModO2 B) := Nat.card_pos
    have := h1.symm.trans h2
    exact (Nat.eq_of_mul_eq_mul_left hpos this).ge
  have heq : V = CFSG.pCore 2 ↥B := Subgroup.eq_of_le_of_card_ge hle hcard
  have e : (↥B ⧸ V) ≃* ModO2 B := QuotientGroup.quotientMulEquivOfEq heq
  obtain ⟨-, K4, _, _, hK4, ⟨e4⟩⟩ := hPY
  obtain ⟨-, K3, _, _, hK3, ⟨e3⟩⟩ := h.psl
  exact B69.not_equiv_sl_four_psl_three (K := K4) (F := K3) (by rw [hK4]; norm_num)
    (by rw [hK3]; norm_num) (e.symm.trans e4) e3

theorem ModL34.isSporadic_M23_of_a312Case
    (h : ModL34 B)
    (hc : A312Case B L) : IsSporadic .M23 ↥L := by
  have hE2 : ∀ k, ∀ (V : Type) [Group V], IsE2 k V → IsPGroup 2 V := fun k V _ h =>
    isPGroup_of_isE2 h
  have hX2 : ∀ k, ∀ (V : Type) [Group V], IsExtraspecial2 k V → IsPGroup 2 V := fun k V _ h =>
    isPGroup_of_isExtraspecial2 h
  have hA5 : ∀ (Y : Type) [Group Y], IsAlt 5 Y → Nat.card Y = 60 := fun Y _ h => card_alt5 h
  have hA6 : ∀ (Y : Type) [Group Y], IsAlt 6 Y → Nat.card Y = 360 := fun Y _ h => card_alt6 h
  have hH6 : ∀ (Y : Type) [Group Y], IsHat Y (alternatingGroup (Fin 6)) → Nat.card Y = 1080 :=
    fun Y _ h => card_hat6 h
  have hL32 : ∀ (Y : Type) [Group Y], IsPSL 3 2 1 Y → Nat.card Y = 168 := fun Y _ h =>
    card_of_isPSL_three_two h
  have hmod := h.card
  rcases hc with h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' |
    h' | h' | h'
  ·
    obtain ⟨⟨n, hn⟩, -, -⟩ := h'
    exact (psl22_ne_20160 n ((card_of_isPSL_two_two hn).2.symm.trans hmod)).elim
  ·
    obtain ⟨f, hf, -, -⟩ := h'
    exact (not_three_dvd_card_of_isSz' hf (by rw [hmod]; norm_num)).elim
  ·
    exact absurd ((card_of_isPSL_three_two h'.1).symm.trans hmod) (by norm_num)
  ·
    exact (h.false_of_modO2_L42 h'.1).elim
  ·
    rcases h'.1 with hB | hB
    · exact (h.false_of_card (by norm_num) (card_alt5 hB)).elim
    · exact (h.false_of_card (by norm_num) (card_of_isPSL_three_two hB)).elim
  ·
    rcases h' with ⟨hB, -⟩ | ⟨hB, -⟩
    · exact (h.false_of_card (by norm_num) (card_alt6 hB)).elim
    · exact (h.false_of_card (by norm_num) (card_hat6 hB)).elim
  ·
    rcases h' with ⟨p, hp, hp3, hB, -⟩ | ⟨hB, -⟩
    · obtain ⟨j, hj⟩ := h.exists_card
      have h2 := card_of_isPSL_two_odd hp (by omega) hB
      refine (false_of_eq_psl2 hp (five_le_of_prime hp hp3) (j := j + 1) ?_).elim
      rw [pow_succ, ← mul_assoc, hj, Nat.mul_comm (Nat.card ↥B) 2]
      exact h2
    · exact (h.false_of_card (by norm_num) (card_alt5 hB)).elim
  ·
    rcases h' with ⟨s, p, hp, hp3, hB, -⟩ | ⟨hB, -⟩ | ⟨hB, -⟩
    · obtain ⟨j, hj⟩ := h.exists_card
      exact (false_of_eq_psl2 hp (five_le_of_prime hp hp3)
        (hj.trans (card_of_isSL2' hp hB))).elim
    · exact (h.false_of_card (by norm_num) (card_alt6 hB)).elim
    · exact (h.false_of_card (by norm_num) (card_hat6 hB)).elim
  ·
    obtain ⟨p, hp, hp3, ⟨V, hVn, hV, hY⟩, -⟩ := h'
    have hp5 := five_le_of_prime hp hp3
    have hV2 : Nat.card V = p ^ 2 := by
      obtain ⟨e⟩ := hV
      rw [Nat.card_congr e.toEquiv]
      change Nat.card (Fin 2 → ZMod p) = p ^ 2
      have : NeZero p := ⟨hp.ne_zero⟩
      rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    have hVodd : Odd (Nat.card V) := by
      rw [hV2]
      exact (hp.odd_of_ne_two (by omega)).pow
    obtain ⟨k, ⟨N, hN, hne, hcard⟩, -⟩ :=
      init_of_odd_ext hp (by omega) hVodd (card_of_isSL2' hp hY)
    have := h.simple
    rcases hN.eq_bot_or_eq_top with hb | ht
    · rw [hb, Subgroup.card_bot, hV2] at hcard
      have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
      omega
    · exact (hne ht).elim
  ·
    exact (h.false_of_card (by norm_num) (card_alt6 h'.1)).elim
  ·
    rcases h' with ⟨hB | hB, -⟩ | ⟨hB | hB, -⟩
    · exact (h.false_of_ext hB (hE2 4) (by norm_num) hA5).elim
    · exact (h.false_of_ext hB (hE2 4) (by norm_num) hA6).elim
    · exact (h.false_of_ext hB (hE2 4) (by norm_num) hA5).elim
    · exact (h.false_of_ext hB (hE2 4) (by norm_num) hH6).elim
  ·
    exact h'.2
  ·
    rcases h'.1 with hB | hB | hB | hB
    · exact (h.false_of_ext_L42 hB (hE2 4)).elim
    · exact (h.false_of_ext hB (hE2 6) (by norm_num) hL32).elim
    · exact (h.false_of_ext hB (hX2 3) (by norm_num) hL32).elim
    · exact (h.false_of_ext hB (hE2 6) (by norm_num) hH6).elim
  ·
    exact (h.false_of_card (by norm_num) (card_alt5 h'.1)).elim
  ·
    exact (h.false_of_ext h'.1 (hX2 2) (by norm_num) hA5).elim
  ·
    rcases h'.2 with hB | hB | hB | hB | hB | hB
    · exact (h.false_of_ext_eleven hB (hX2 6) (by norm_num)
        (fun Y _ h => card_hatM22 h)).elim
    · exact (h.false_of_ext_eleven hB (hE2 11) (by norm_num)
        (fun Y _ h => card_of_isSporadic_M24' h)).elim
    · exact absurd ((card_alt5 hB).symm.trans hmod) (by norm_num)
    · exact absurd ((card_hat6 hB).symm.trans hmod) (by norm_num)
    · exact (h.false_of_modO2_L42 hB).elim
    · exact absurd ((card_of_isPSL_three_two hB).symm.trans hmod) (by norm_num)
  ·
    rcases h'.1 with hB | hB
    · exact (h.false_of_ext hB (fun V _ h => isPGroup_of_isZ4StarExtra2 h) (by norm_num)
        hA5).elim
    · exact (h.false_of_ext hB (fun V _ h => isPGroup_of_isZ4Cubed h) (by norm_num)
        hL32).elim
  ·
    rcases h'.1 with hB | hB
    · exact (h.false_of_ext hB (hX2 3) (by norm_num) hL32).elim
    · exact (h.false_of_ext hB (hE2 6) (by norm_num) hH6).elim
  ·
    rcases h'.1 with hB | hB
    · exact absurd ((card_alt5 hB).symm.trans hmod) (by norm_num)
    · exact absurd ((card_of_isPSL_three_two hB).symm.trans hmod) (by norm_num)

theorem ModL34.false_of_a312Nonquasi (h : ModL34 B) (hBL : B ≤ L) (hperf : Group.IsPerfect ↥B)
    (hc : A312Nonquasi B L) : False := by
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
  have : (OL.subgroupOf (B ⊔ OL)).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hBO
  have hφ : Nat.card (↥B ⧸ V) = (OL.subgroupOf (B ⊔ OL)).index :=
    Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient B OL hBO).toEquiv
  obtain ⟨p, hp, hp5, hcard⟩ : ∃ p, p.Prime ∧ 5 ≤ p ∧ Nat.card (↥B ⧸ V) = p * (p ^ 2 - 1) := by
    have hpq : Group.IsPerfect (↥B ⧸ V) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' V) (QuotientGroup.mk'_surjective _)
    unfold A312Nonquasi at hc
    dsimp only at hc
    rcases hc with ⟨-, hLB, p, hp, hp2, hSL⟩ | ⟨-, -, N, hN, rfl, hSL⟩
    · have hc' : Nat.card (↥B ⧸ V) = p * (p ^ 2 - 1) := by
        rw [hφ, ← hLB, hsub]
        exact card_of_isSL2' hp hSL
      have hp5 : 5 ≤ p := by
        by_contra hlt
        have hp3 : p = 3 := by
          have := hp.two_le
          interval_cases p <;> first | rfl | exact absurd rfl hp2 | exact absurd hp (by decide)
        subst hp3
        exact false_of_perfect_card_24 hpq (hc'.trans (by norm_num))
      exact ⟨p, hp, hp5, hc'⟩
    · refine ⟨5, by norm_num, le_rfl, ?_⟩
      rw [hφ]
      exact card_of_isSL2' (by norm_num) hSL
  obtain ⟨k, ⟨N, hN, hne, hcardN⟩, hk⟩ := init_of_odd_ext hp hp5 hVodd hcard
  have := h.simple
  rcases hN.eq_bot_or_eq_top with hb | ht
  · rw [hb, Subgroup.card_bot] at hcardN
    rw [h.card, ← hcardN, one_mul] at hk
    exact false_of_eq_psl2 hp hp5 hk
  · exact hne ht

end CFSG.Quasithin.H13.A5
