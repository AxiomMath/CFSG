module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma3Cs

public section

namespace CFSG.Quasithin.H13.KG12614

open CFSG.Open CFSG.Blueprint

structure DataA6 (X : Type) [Group X] : Prop where
  cardQ : Nat.card (X ⧸ CFSG.pCore 2 X) = 360
  card : ∃ a, Nat.card X = 2 ^ a * 360
  quot : ∀ V : Subgroup X, V.Normal → IsPGroup 2 ↥V → ∃ j, Nat.card (X ⧸ V) = 2 ^ j * 360

variable {X : Type} [Group X]

theorem dataA6_of [Finite X] (φ : X →* ↥(alternatingGroup (Fin 6))) (hφ : Function.Surjective φ)
    (hker : φ.ker = CFSG.pCore 2 X) : DataA6 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h360 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    decide
  have hcQ : Nat.card (X ⧸ CFSG.pCore 2 X) = 360 := by
    rw [← h360, ← hker]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv
  have hX : Nat.card X = Nat.card (X ⧸ CFSG.pCore 2 X) * Nat.card (CFSG.pCore 2 X) :=
    (CFSG.pCore 2 X).card_eq_card_quotient_mul_card_subgroup
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := X))
  refine ⟨hcQ, ⟨a, by rw [hX, ha, hcQ, mul_comm]⟩, fun V hVn hV2 => ?_⟩
  have hle : V ≤ CFSG.pCore 2 X := le_sSup ⟨hVn, hV2⟩
  obtain ⟨t, ht⟩ := Subgroup.card_dvd_of_le hle
  have ht2 : t ∣ 2 ^ a := ⟨Nat.card ↥V, by rw [← ha, ht, mul_comm]⟩
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 ht2
  refine ⟨j, ?_⟩
  have h1 := V.card_eq_card_quotient_mul_card_subgroup
  have hV0 : 0 < Nat.card ↥V := Nat.card_pos
  have h2 : Nat.card (X ⧸ V) * Nat.card ↥V = (2 ^ j * 360) * Nat.card ↥V := by
    rw [← h1, hX, ht, hcQ]
    ring
  exact Nat.eq_of_mul_eq_mul_right hV0 h2

theorem eq_five_of_dvd {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (h : p ∣ 360) : p = 5 := by
  have h' : p ∣ 2 ^ 3 * 3 ^ 2 * 5 := by norm_num; exact h
  rcases (Nat.Prime.dvd_mul hp).1 h' with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2)
      omega
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h2)
      omega
  · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 h1

theorem dvd_of_odd_dvd {q j : ℕ} (hq : Odd q) (h : q ∣ 2 ^ j * 360) : q ∣ 360 :=
  Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.pow_right j (Nat.coprime_two_right.2 hq)) h

theorem ne_of_lt {c j : ℕ} (hc : c < 360) : c ≠ 2 ^ j * 360 := by
  have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  intro h
  have : 360 ≤ 2 ^ j * 360 := by nlinarith
  omega

theorem ne_of_odd_dvd {c j q : ℕ} (hq : Odd q) (hqc : q ∣ c) (h360 : ¬ q ∣ 360) :
    c ≠ 2 ^ j * 360 := fun h => h360 (dvd_of_odd_dvd hq (h ▸ hqc))

namespace DataA6

variable (hD : DataA6 X)
include hD

theorem le_card : 360 ≤ Nat.card X := by
  obtain ⟨a, ha⟩ := hD.card
  have : 1 ≤ 2 ^ a := Nat.one_le_two_pow
  rw [ha]
  nlinarith

theorem false_of_card_lt {c : ℕ} (h : Nat.card X = c) (hc : c < 360) : False := by
  have := hD.le_card
  omega

theorem false_of_odd_dvd {q : ℕ} (hq : Odd q) (h : q ∣ Nat.card X) (h360 : ¬ q ∣ 360) : False := by
  obtain ⟨a, ha⟩ := hD.card
  exact ne_of_odd_dvd hq (ha ▸ h) h360 rfl

theorem eq_five {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (h : p ∣ Nat.card X) : p = 5 := by
  obtain ⟨a, ha⟩ := hD.card
  exact eq_five_of_dvd hp hp3 (dvd_of_dvd_two_pow_mul hp hp3 (ha ▸ h))

theorem false_of_isExt [Finite X] {PV PY : ∀ (V : Type) [Group V], Prop} (h : IsExt X PV PY)
    (hPV : ∀ (V : Type) [Group V] [Finite V], PV V → ∃ m, Nat.card V = 2 ^ m)
    (hPY : ∀ (Y : Type) [Group Y] [Finite Y], PY Y → ∀ j, Nat.card Y ≠ 2 ^ j * 360) : False := by
  obtain ⟨V, hVn, hpv, hpy⟩ := h
  obtain ⟨m, hm⟩ := hPV _ hpv
  obtain ⟨j, hj⟩ := hD.quot V hVn (IsPGroup.of_card hm)
  exact hPY _ hpy j hj

end DataA6

section Orders

variable {Y : Type} [Group Y]

theorem ne_of_isAlt5 (h : IsAlt 5 Y) (j : ℕ) : Nat.card Y ≠ 2 ^ j * 360 :=
  card_alt_five h ▸ ne_of_lt (by norm_num)

theorem ne_of_isHat6 (h : IsHat Y ↥(alternatingGroup (Fin 6))) (j : ℕ) :
    Nat.card Y ≠ 2 ^ j * 360 :=
  card_hat_six h ▸ ne_of_odd_dvd (q := 27) (by decide) (by norm_num) (by norm_num)

theorem ne_of_isPSL321 (h : IsPSL 3 2 1 Y) (j : ℕ) : Nat.card Y ≠ 2 ^ j * 360 :=
  Vol2.Ch11.SecB.card_isPSL_three_two_one h ▸ ne_of_lt (by norm_num)

theorem ne_of_isPSL421 (h : IsPSL 4 2 1 Y) (j : ℕ) : Nat.card Y ≠ 2 ^ j * 360 := by
  obtain ⟨e⟩ := nonempty_mulEquiv_sl_of_isPSL h
  rw [Nat.card_congr e.toEquiv, card_sl_four_zmod_two]
  exact ne_of_odd_dvd (q := 7) (by decide) (by norm_num) (by norm_num)

theorem ne_of_isHatM22 (h : IsHat Y (NativeSporadic.Carrier .M22)) (j : ℕ) :
    Nat.card Y ≠ 2 ^ j * 360 := by
  rw [Vol2.Ch11.SecA.card_of_isHat h]
  exact ne_of_odd_dvd (q := 11) (by decide)
    (Vol2.Ch11.SecA.eleven_dvd_card_M22.mul_right 3) (by norm_num)

theorem ne_of_isM24 (h : IsSporadic .M24 Y) (j : ℕ) : Nat.card Y ≠ 2 ^ j * 360 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  exact ne_of_odd_dvd (q := 23) (by decide) Vol2.Ch11.SecA.twentythree_dvd_card_M24
    (by norm_num)

end Orders

variable {Q : Type} [Group Q] [Finite Q] {B L : Subgroup Q}

theorem card_e2 (n : ℕ) : ∀ (V : Type) [Group V] [Finite V], IsE2 n V → ∃ m, Nat.card V = 2 ^ m :=
  fun _ _ _ h => ⟨n, Vol2.Ch11.SecA.card_isE2 h⟩

theorem card_extra (n : ℕ) :
    ∀ (V : Type) [Group V] [Finite V], IsExtraspecial2 n V → ∃ m, Nat.card V = 2 ^ m :=
  fun _ _ _ h => ⟨1 + 2 * n, Vol2.Ch11.SecA.card_isExtraspecial2 h⟩

theorem cases_of_a312 (hD : DataA6 ↥B) (h : A312Case B L) :
    (IsAlt 6 ↥B ∧ (IsAlt 7 ↥L ∨ IsPSU 3 5 1 ↥L ∨ IsSporadic .M11 ↥L)) ∨
      IsSporadic .M22 ↥L ∨ IsSporadic .M23 ↥L := by
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  ·
    exfalso
    obtain ⟨⟨m, hm⟩, -, -⟩ := h
    obtain ⟨hm1, hcard⟩ := Vol2.Ch11.SecA.card_of_isPSL_two_two hm
    rw [hD.cardQ] at hcard
    exact Vol2.Ch11.SecA.oSL2_ne_45 (Vol2.Ch11.SecA.eq_of_two_pow_mul_eq
      (Vol2.Ch11.SecA.odd_oSL2 hm1) (by decide)
      (hcard.symm.trans (show (360 : ℕ) = 2 ^ 3 * 45 by norm_num)))
  ·
    exfalso
    obtain ⟨f, hf, -⟩ := h
    have h3 := Vol2.Ch11.SecA.not_three_dvd_card_of_isSz hf
    rw [hD.cardQ] at h3
    exact h3 (by norm_num)
  ·
    exfalso
    have := Vol2.Ch11.SecB.card_isPSL_three_two_one h.1
    rw [hD.cardQ] at this
    norm_num at this
  ·
    exfalso
    exact ne_of_isPSL421 h.1 0 (by rw [hD.cardQ]; norm_num)
  ·
    exfalso
    rcases h.1 with hB | hB
    · exact hD.false_of_card_lt (card_alt_five hB) (by norm_num)
    · exact hD.false_of_card_lt (Vol2.Ch11.SecB.card_isPSL_three_two_one hB) (by norm_num)
  ·
    rcases h with ⟨hB, hL⟩ | ⟨hB, -⟩
    · exact Or.inl ⟨hB, Or.inl hL⟩
    · exact (hD.false_of_odd_dvd (q := 27) (by decide) (by rw [card_hat_six hB]; norm_num)
        (by norm_num)).elim
  ·
    exfalso
    rcases h with ⟨p, hp, hp3, hB, -⟩ | ⟨hB, -⟩
    · have h2 := Vol2.Ch11.SecA.two_mul_card_of_isPSL_two hp (by omega) hB
      have hpB : p ∣ Nat.card ↥B := by
        have : p ∣ 2 * Nat.card ↥B := h2 ▸ dvd_mul_right p _
        exact (Nat.Coprime.dvd_of_dvd_mul_left
          ((Nat.coprime_primes hp Nat.prime_two).2 (by omega)) this)
      have hp5 := hD.eq_five hp hp3 hpB
      subst hp5
      exact hD.false_of_card_lt (c := 60) (by omega) (by norm_num)
    · exact hD.false_of_card_lt (card_alt_five hB) (by norm_num)
  ·
    rcases h with ⟨s, p, hp, hp3, hB, -⟩ | ⟨hB, hL⟩ | ⟨hB, -⟩
    · exfalso
      have hc := Vol2.Ch11.SecA.card_of_isSL2 hp hB
      have hp5 := hD.eq_five hp hp3 (hc ▸ dvd_mul_right p _)
      subst hp5
      exact hD.false_of_card_lt hc (by norm_num)
    · exact Or.inl ⟨hB, Or.inr (Or.inl hL)⟩
    · exact (hD.false_of_odd_dvd (q := 27) (by decide) (by rw [card_hat_six hB]; norm_num)
        (by norm_num)).elim
  ·
    exfalso
    obtain ⟨p, hp, hp3, ⟨V, hVn, hV, hY⟩, -⟩ := h
    have h1 := V.card_eq_card_quotient_mul_card_subgroup
    rw [card_elemAbelian_two hV, Vol2.Ch11.SecA.card_of_isSL2 hp hY] at h1
    have hp5 := hD.eq_five hp hp3 (h1 ▸ (dvd_mul_right p _).mul_right _)
    subst hp5
    exact hD.false_of_odd_dvd (q := 25) (by decide) (h1 ▸ dvd_mul_left _ _) (by norm_num)
  ·
    exact Or.inl ⟨h.1, Or.inr (Or.inr h.2)⟩
  ·
    rcases h with ⟨-, hL⟩ | ⟨hB, -⟩
    · exact Or.inr (Or.inl hL)
    · exfalso
      rcases hB with hB | hB
      · exact hD.false_of_isExt hB (card_e2 4) fun _ _ _ hY j => ne_of_isAlt5 hY j
      · exact hD.false_of_isExt hB (card_e2 4) fun _ _ _ hY j => ne_of_isHat6 hY j
  ·
    exact Or.inr (Or.inr h.2)
  ·
    exfalso
    rcases h.1 with hB | hB | hB | hB
    · exact hD.false_of_isExt hB (card_e2 4) fun _ _ _ hY j => ne_of_isPSL421 hY j
    · exact hD.false_of_isExt hB (card_e2 6) fun _ _ _ hY j => ne_of_isPSL321 hY j
    · exact hD.false_of_isExt hB (card_extra 3) fun _ _ _ hY j => ne_of_isPSL321 hY j
    · exact hD.false_of_isExt hB (card_e2 6) fun _ _ _ hY j => ne_of_isHat6 hY j
  ·
    exact (hD.false_of_card_lt (card_alt_five h.1) (by norm_num)).elim
  ·
    exact (hD.false_of_isExt h.1 (card_extra 2) fun _ _ _ hY j => ne_of_isAlt5 hY j).elim
  ·
    exfalso
    rcases h.2 with hB | hB | hB | hB | hB | hB
    · exact hD.false_of_isExt hB (card_extra 6) fun _ _ _ hY j => ne_of_isHatM22 hY j
    · exact hD.false_of_isExt hB (card_e2 11) fun _ _ _ hY j => ne_of_isM24 hY j
    · exact ne_of_isAlt5 hB 0 (by rw [hD.cardQ]; norm_num)
    · exact ne_of_isHat6 hB 0 (by rw [hD.cardQ]; norm_num)
    · exact ne_of_isPSL421 hB 0 (by rw [hD.cardQ]; norm_num)
    · exact ne_of_isPSL321 hB 0 (by rw [hD.cardQ]; norm_num)
  ·
    exfalso
    rcases h.1 with hB | hB
    · exact hD.false_of_isExt hB (fun _ _ _ h => Vol2.Ch11.SecA.card_isZ4StarExtra2 h)
        fun _ _ _ hY j => ne_of_isAlt5 hY j
    · exact hD.false_of_isExt hB (fun _ _ _ h => ⟨6, Vol2.Ch11.SecA.card_isZ4Cubed h⟩)
        fun _ _ _ hY j => ne_of_isPSL321 hY j
  ·
    exfalso
    rcases h.1 with hB | hB
    · exact hD.false_of_isExt hB (card_extra 3) fun _ _ _ hY j => ne_of_isPSL321 hY j
    · exact hD.false_of_isExt hB (card_e2 6) fun _ _ _ hY j => ne_of_isHat6 hY j
  ·
    exfalso
    rcases h.1 with hB | hB
    · exact ne_of_isAlt5 hB 0 (by rw [hD.cardQ]; norm_num)
    · exact ne_of_isPSL321 hB 0 (by rw [hD.cardQ]; norm_num)

end CFSG.Quasithin.H13.KG12614
