module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113Lie
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma3Cs
import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

variable {Q : Type} [Group Q]

structure Data513 (B : Subgroup Q) (c : ℕ) : Prop where
  c_mem : c = 2520 ∨ c = 604800 ∨ c = 10200960
  cardQ : Nat.card (ModO2 B) = c
  card : ∃ a, Nat.card ↥B = 2 ^ a * c
  dvd : ∀ V : Subgroup ↥B, V.Normal → IsPGroup 2 ↥V → c ∣ Nat.card (↥B ⧸ V)

theorem data513_of [Finite Q] {B : Subgroup Q} {c : ℕ} (hc : c = 2520 ∨ c = 604800 ∨ c = 10200960)
    (hcQ : Nat.card (ModO2 B) = c) : Data513 B c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB : Nat.card ↥B = Nat.card (ModO2 B) * Nat.card (CFSG.pCore 2 ↥B) :=
    (CFSG.pCore 2 ↥B).card_eq_card_quotient_mul_card_subgroup
  refine ⟨hc, hcQ, ?_, ?_⟩
  · obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥B))
    exact ⟨a, by rw [hB, ha, hcQ, mul_comm]⟩
  · intro V hVn hV2
    have hle : V ≤ CFSG.pCore 2 ↥B := le_sSup ⟨hVn, hV2⟩
    obtain ⟨t, ht⟩ := Subgroup.card_dvd_of_le hle
    have h1 := V.card_eq_card_quotient_mul_card_subgroup
    refine ⟨t, ?_⟩
    have hV0 : 0 < Nat.card ↥V := Nat.card_pos
    have h2 : Nat.card (↥B ⧸ V) * Nat.card ↥V = (c * t) * Nat.card ↥V := by
      rw [← h1, hB, ht, hcQ]
      ring
    exact Nat.eq_of_mul_eq_mul_right hV0 h2

namespace Data513

variable {B : Subgroup Q} {c : ℕ}

theorem dvd_c (hD : Data513 B c) : 2520 ∣ c := by
  rcases hD.c_mem with rfl | rfl | rfl <;> norm_num

theorem false_of_dvd (hD : Data513 B c) {m : ℕ} (h : c ∣ m) (hm : ¬ 2520 ∣ m) : False :=
  hm (hD.dvd_c.trans h)

theorem dvd_card (hD : Data513 B c) : c ∣ Nat.card ↥B := by
  obtain ⟨a, ha⟩ := hD.card
  exact ⟨2 ^ a, by rw [ha, mul_comm]⟩

theorem false_of_card (hD : Data513 B c) {m : ℕ} (h : Nat.card ↥B = m) (hm : ¬ 2520 ∣ m) :
    False :=
  hD.false_of_dvd (h ▸ hD.dvd_card) hm

theorem false_of_eq (hD : Data513 B c) {m : ℕ} (h : c = m)
    (hm : m ≠ 2520 ∧ m ≠ 604800 ∧ m ≠ 10200960) : False := by
  rcases hD.c_mem with rfl | rfl | rfl <;> omega

theorem odd_part (hD : Data513 B c) {e m : ℕ} (hm : Odd m) (h : Nat.card ↥B = 2 ^ e * m) :
    m = 315 ∨ m = 4725 ∨ m = 79695 := by
  obtain ⟨a, ha⟩ := hD.card
  rw [ha] at h
  rcases hD.c_mem with rfl | rfl | rfl
  · left
    exact (Vol2.Ch11.SecA.eq_of_two_pow_mul_eq (a := a + 3) (b := e) (by decide) hm
      (by rw [← h, pow_add]; ring)).symm
  · right; left
    exact (Vol2.Ch11.SecA.eq_of_two_pow_mul_eq (a := a + 7) (b := e) (by decide) hm
      (by rw [← h, pow_add]; ring)).symm
  · right; right
    exact (Vol2.Ch11.SecA.eq_of_two_pow_mul_eq (a := a + 7) (b := e) (by decide) hm
      (by rw [← h, pow_add]; ring)).symm

theorem dvd_of_isExt [Finite Q] (hD : Data513 B c) {PV PY : ∀ (V : Type) [Group V], Prop}
    (h : IsExt ↥B PV PY)
    (hPV : ∀ (V : Type) [Group V] [Finite V], PV V → ∃ m, Nat.card V = 2 ^ m) :
    ∃ (V : Subgroup ↥B) (_ : V.Normal), PY (↥B ⧸ V) ∧ c ∣ Nat.card (↥B ⧸ V) ∧
      ∃ m, Nat.card ↥B = 2 ^ m * Nat.card (↥B ⧸ V) := by
  obtain ⟨V, hVn, hpv, hpy⟩ := h
  obtain ⟨m, hm⟩ := hPV _ hpv
  refine ⟨V, hVn, hpy, hD.dvd V hVn (IsPGroup.of_card hm), m, ?_⟩
  rw [V.card_eq_card_quotient_mul_card_subgroup, hm, mul_comm]

theorem eq_of_simple_quot [Finite Q] (hD : Data513 B c) {V : Subgroup ↥B} [hVn : V.Normal]
    (hV2 : IsPGroup 2 ↥V) (hs : IsSimpleGroup (↥B ⧸ V)) (hn2 : ¬ IsPGroup 2 (↥B ⧸ V)) :
    c = Nat.card (↥B ⧸ V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.pCore 2 ↥B with hO
  have hVO : V ≤ O := le_sSup ⟨hVn, hV2⟩
  have hO2 : IsPGroup 2 ↥O := CFSG.pCore_isPGroup (p := 2) (G := ↥B)
  have hOn : O.Normal := CFSG.pCore_normal
  have himg : (O.map (QuotientGroup.mk' V)).Normal :=
    Subgroup.Normal.map hOn _ (QuotientGroup.mk'_surjective _)
  have hOV : O ≤ V := by
    rcases himg.eq_bot_or_eq_top with hbot | htop
    · intro x hx
      have h1 : QuotientGroup.mk' V x ∈ O.map (QuotientGroup.mk' V) := ⟨x, hx, rfl⟩
      rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    · exfalso
      apply hn2
      have h2 : IsPGroup 2 ↥(O.map (QuotientGroup.mk' V)) := hO2.map _
      rw [htop] at h2
      exact h2.of_equiv Subgroup.topEquiv
  have hOeq : O = V := le_antisymm hOV hVO
  rw [← hD.cardQ]
  exact Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hOeq).toEquiv

end Data513

theorem prime_cases_of_dvd {p c : ℕ} (hc : c = 2520 ∨ c = 604800 ∨ c = 10200960) (hp : p.Prime)
    (hp3 : 3 < p) (h : p ∣ c) : p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 23 := by
  have hdvd : p ∣ 2 ^ 7 * 3 ^ 3 * 5 ^ 2 * 7 * 11 * 23 :=
    h.trans (by rcases hc with rfl | rfl | rfl <;> norm_num)
  have hp2 : p ≠ 2 := by omega
  have hp3' : p ≠ 3 := by omega
  rcases (Nat.Prime.dvd_mul hp).1 hdvd with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
      · rcases (Nat.Prime.dvd_mul hp).1 h3 with h4 | h4
        · rcases (Nat.Prime.dvd_mul hp).1 h4 with h5 | h5
          · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
              (hp.dvd_of_dvd_pow h5)) hp2
          · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1
              (hp.dvd_of_dvd_pow h5)) hp3'
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 (hp.dvd_of_dvd_pow h4))
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h3))
    · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h2)))
  · exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h1)))

theorem false_of_card_sl2 {p b c : ℕ} (hc : c = 2520 ∨ c = 604800 ∨ c = 10200960)
    (hp : p.Prime) (hp3 : 3 < p) (h : p * (p ^ 2 - 1) = 2 ^ b * c) : False := by
  have hpc : p ∣ c := dvd_of_dvd_two_pow_mul hp hp3 (h ▸ dvd_mul_right p _)
  have hx : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  rcases prime_cases_of_dvd hc hp hp3 hpc with rfl | rfl | rfl | rfl <;>
  · norm_num at h
    generalize 2 ^ b = x at h hx
    rcases hc with rfl | rfl | rfl <;> omega

theorem false_of_card_ext_sl2' {p b c : ℕ} (hc : c = 2520 ∨ c = 604800 ∨ c = 10200960)
    (hp : p.Prime) (hp3 : 3 < p) (h : p * (p ^ 2 - 1) * p ^ 2 = 2 ^ b * c) : False := by
  have hp3c : p ^ 3 ∣ c := by
    have h1 : p ^ 3 ∣ 2 ^ b * c := h ▸ ⟨p ^ 2 - 1, by ring⟩
    exact Nat.Coprime.dvd_of_dvd_mul_left
      (Nat.Coprime.pow 3 b ((Nat.coprime_primes hp Nat.prime_two).2 (by omega))) h1
  have hpc : p ∣ c := (dvd_pow_self p (by norm_num)).trans hp3c
  rcases prime_cases_of_dvd hc hp hp3 hpc with rfl | rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl <;> norm_num at hp3c

theorem not_isPGroup_two_of_card_odd {X : Type} [Group X] [Finite X] {e m : ℕ} (hm : Odd m)
    (hm1 : m ≠ 1) (h : Nat.card X = 2 ^ e * m) : ¬ IsPGroup 2 X := by
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h2
  have := Vol2.Ch11.SecA.eq_of_two_pow_mul_eq (a := k) (b := e) (m := 1) odd_one hm
    (by rw [mul_one, ← hk, h])
  exact hm1 this.symm

theorem card_isPSL_four_two_one {X : Type} [Group X] (h : IsPSL 4 2 1 X) :
    Nat.card X = 20160 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_four_two h

theorem simple_of_l42_or_l34 {X : Type} [Group X] [Finite X]
    (h : IsPSL 4 2 1 X ∨ IsPSL 3 2 2 X) : IsSimpleGroup X ∧ ¬ IsPGroup 2 X := by
  have hs : IsSimpleGroup X := by
    rcases h with h | h
    · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity X 4 2 1 h).2
    · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity X 3 2 2 h).2
  refine ⟨hs, not_isPGroup_two_of_card_odd (e := 6) (m := 315) (by decide) (by norm_num) ?_⟩
  rcases h with h | h
  · rw [card_isPSL_four_two_one h]; norm_num
  · rw [Vol2.Ch11.SecB.card_isPSL_three_two_two h]; norm_num

theorem card_isSporadic_M22 {X : Type} [Group X]
    (h : IsSporadic .M22 X) : Nat.card X = 443520 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.Sporadic.Mathieu.card_M22

theorem card_hat_M22 {X : Type} [Group X]
    (h : IsHat X (NativeSporadic.Carrier .M22)) : Nat.card X = 1330560 := by
  rw [Vol2.Ch11.SecA.card_of_isHat h]
  change Nat.card ↥NativeSporadic.M22 * 3 = 1330560
  rw [CFSG.Sporadic.Mathieu.card_M22]

theorem card_isSporadic_M24 {X : Type} [Group X]
    (h : IsSporadic .M24 X) : Nat.card X = 244823040 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.Sporadic.Mathieu.card_M24

namespace Data513

variable [Finite Q] {B L : Subgroup Q} {c : ℕ}

theorem pow_of_isE2 {k : ℕ} : ∀ (V : Type) [Group V] [Finite V], IsE2 k V →
    ∃ m, Nat.card V = 2 ^ m :=
  fun _ _ _ h => ⟨k, Vol2.Ch11.SecA.card_isE2 h⟩

theorem pow_of_isExtraspecial2 {k : ℕ} : ∀ (V : Type) [Group V] [Finite V],
    IsExtraspecial2 k V → ∃ m, Nat.card V = 2 ^ m :=
  fun _ _ _ h => ⟨1 + 2 * k, Vol2.Ch11.SecA.card_isExtraspecial2 h⟩

theorem of_case
    (hD : Data513 B c) (h : A312Case B L) :
    c = 2520 ∧ IsSporadic .M23 ↥L := by
  have hc := hD.c_mem
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  ·
    obtain ⟨⟨m, hm⟩, -, -⟩ := h
    obtain ⟨hm1, hcard⟩ := Vol2.Ch11.SecA.card_of_isPSL_two_two hm
    rw [hD.cardQ] at hcard
    have ho := Vol2.Ch11.SecA.odd_oSL2 hm1
    exfalso
    rcases hc with rfl | rfl | rfl
    · exact Vol2.Ch11.SecA.oSL2_ne_315 (Vol2.Ch11.SecA.eq_of_two_pow_mul_eq ho (by decide)
        (hcard.symm.trans (show (2520 : ℕ) = 2 ^ 3 * 315 by norm_num)))
    · exact Vol2.Ch11.SecA.oSL2_ne (k := 7) (by decide) (by decide)
        (Vol2.Ch11.SecA.eq_of_two_pow_mul_eq ho (by decide)
          (hcard.symm.trans (show (604800 : ℕ) = 2 ^ 7 * 4725 by norm_num)))
    · exact Vol2.Ch11.SecA.oSL2_ne (k := 9) (by decide) (by decide)
        (Vol2.Ch11.SecA.eq_of_two_pow_mul_eq ho (by decide)
          (hcard.symm.trans (show (10200960 : ℕ) = 2 ^ 7 * 79695 by norm_num)))
  ·
    obtain ⟨f, hf, -⟩ := h
    have h3 := Vol2.Ch11.SecA.not_three_dvd_card_of_isSz hf
    rw [hD.cardQ] at h3
    exact (h3 (by rcases hc with rfl | rfl | rfl <;> norm_num)).elim
  ·
    exact (hD.false_of_eq (hD.cardQ.symm.trans (Vol2.Ch11.SecB.card_isPSL_three_two_one h.1))
      (by norm_num)).elim
  ·
    exact (hD.false_of_eq (hD.cardQ.symm.trans (card_isPSL_four_two_one h.1))
      (by norm_num)).elim
  ·
    rcases h.1 with hB | hB
    · exact (hD.false_of_card (card_alt_five hB) (by norm_num)).elim
    · exact (hD.false_of_card (Vol2.Ch11.SecB.card_isPSL_three_two_one hB) (by norm_num)).elim
  ·
    rcases h with ⟨hB, -⟩ | ⟨hB, -⟩
    · exact (hD.false_of_card (card_alt_six hB) (by norm_num)).elim
    · exact (hD.false_of_card (card_hat_six hB) (by norm_num)).elim
  ·
    rcases h with ⟨p, hp, hp3, hB, -⟩ | ⟨hB, -⟩
    · have h2 := Vol2.Ch11.SecA.two_mul_card_of_isPSL_two hp (by omega) hB
      obtain ⟨a, ha⟩ := hD.card
      exact (false_of_card_sl2 hc hp hp3 (b := a + 1)
        (by rw [← h2, ha, pow_succ]; ring)).elim
    · exact (hD.false_of_card (card_alt_five hB) (by norm_num)).elim
  ·
    rcases h with ⟨s, p, hp, hp3, hB, -⟩ | ⟨hB, -⟩ | ⟨hB, -⟩
    · obtain ⟨a, ha⟩ := hD.card
      exact (false_of_card_sl2 hc hp hp3
        ((Vol2.Ch11.SecA.card_of_isSL2 hp hB).symm.trans ha)).elim
    · exact (hD.false_of_card (card_alt_six hB) (by norm_num)).elim
    · exact (hD.false_of_card (card_hat_six hB) (by norm_num)).elim
  ·
    obtain ⟨p, hp, hp3, ⟨V, hVn, hV, hY⟩, -⟩ := h
    obtain ⟨a, ha⟩ := hD.card
    have h1 := V.card_eq_card_quotient_mul_card_subgroup
    rw [card_elemAbelian_two hV, Vol2.Ch11.SecA.card_of_isSL2 hp hY, ha] at h1
    exact (false_of_card_ext_sl2' hc hp hp3 h1.symm).elim
  ·
    exact (hD.false_of_card (card_alt_six h.1) (by norm_num)).elim
  ·
    exfalso
    rcases h with ⟨hB | hB, -⟩ | ⟨hB | hB, -⟩
    · obtain ⟨V, hVn, hY, hdvd, -⟩ := hD.dvd_of_isExt hB pow_of_isE2
      exact hD.false_of_dvd (card_alt_five hY ▸ hdvd) (by norm_num)
    · obtain ⟨V, hVn, hY, hdvd, -⟩ := hD.dvd_of_isExt hB pow_of_isE2
      exact hD.false_of_dvd (card_alt_six hY ▸ hdvd) (by norm_num)
    · obtain ⟨V, hVn, hY, hdvd, -⟩ := hD.dvd_of_isExt hB pow_of_isE2
      exact hD.false_of_dvd (card_alt_five hY ▸ hdvd) (by norm_num)
    · obtain ⟨V, hVn, hY, hdvd, -⟩ := hD.dvd_of_isExt hB pow_of_isE2
      exact hD.false_of_dvd (card_hat_six hY ▸ hdvd) (by norm_num)
  ·
    obtain ⟨hB, hK⟩ := h
    refine ⟨?_, hK⟩
    rcases hB with hM | hB | hB | hB | hB | hB | hB
    ·
      have := hD.odd_part (e := 7) (m := 3465) (by decide)
        (by rw [card_isSporadic_M22 hM]; norm_num)
      omega
    ·
      exfalso
      obtain ⟨hs, hn2⟩ := simple_of_l42_or_l34 (Or.inr hB)
      have hcB := Vol2.Ch11.SecB.card_isPSL_three_two_two hB
      have h1 : Nat.card ↥B = Nat.card (ModO2 B) * Nat.card (CFSG.pCore 2 ↥B) :=
        (CFSG.pCore 2 ↥B).card_eq_card_quotient_mul_card_subgroup
      rw [hcB, hD.cardQ] at h1
      have hO : CFSG.pCore 2 ↥B = ⊥ ∨ CFSG.pCore 2 ↥B = ⊤ :=
        (CFSG.pCore_normal : (CFSG.pCore 2 ↥B).Normal).eq_bot_or_eq_top
      rcases hO with hO | hO
      · rw [hO, Subgroup.card_bot] at h1
        exact hD.false_of_eq (m := 20160) (by omega) (by norm_num)
      · apply hn2
        have h2 : IsPGroup 2 ↥(CFSG.pCore 2 ↥B) := CFSG.pCore_isPGroup (p := 2) (G := ↥B)
        rw [hO] at h2
        exact h2.of_equiv Subgroup.topEquiv
    ·
      obtain ⟨V, hVn, hY, hdvd, -⟩ := hD.dvd_of_isExt hB pow_of_isE2
      rw [card_alt_seven hY] at hdvd
      rcases hc with rfl | rfl | rfl
      · rfl
      · norm_num at hdvd
      · norm_num at hdvd
    · obtain ⟨V, hVn, hY, hdvd, -⟩ := hD.dvd_of_isExt hB pow_of_isE2
      exact (hD.false_of_dvd (Vol2.Ch11.SecB.card_isPSL_three_two_one hY ▸ hdvd)
        (by norm_num)).elim
    · obtain ⟨V, hVn, hY, hdvd, -⟩ := hD.dvd_of_isExt hB pow_of_isE2
      exact (hD.false_of_dvd (Vol2.Ch11.SecB.card_isPSL_three_two_one hY ▸ hdvd)
        (by norm_num)).elim
    · obtain ⟨V, hVn, hY, hdvd, -⟩ := hD.dvd_of_isExt hB pow_of_isE2
      exact (hD.false_of_dvd (card_alt_six hY ▸ hdvd) (by norm_num)).elim
    · obtain ⟨V, hVn, hY, hdvd, -⟩ := hD.dvd_of_isExt hB pow_of_isE2
      exact (hD.false_of_dvd (card_alt_five hY ▸ hdvd) (by norm_num)).elim
  ·
    exfalso
    obtain ⟨hB, -⟩ := h
    rcases hB with hB | hB | hB | hB
    ·
      obtain ⟨V, hVn, hV, hY⟩ := hB
      obtain ⟨hs, hn2⟩ := simple_of_l42_or_l34 (Or.inl hY)
      have hV2 : IsPGroup 2 ↥V := IsPGroup.of_card (Vol2.Ch11.SecA.card_isE2 hV)
      have := hD.eq_of_simple_quot hV2 hs hn2
      rw [card_isPSL_four_two_one hY] at this
      exact hD.false_of_eq this (by norm_num)
    · obtain ⟨V, hVn, hY, hdvd, -⟩ := hD.dvd_of_isExt hB pow_of_isE2
      exact hD.false_of_dvd (Vol2.Ch11.SecB.card_isPSL_three_two_one hY ▸ hdvd) (by norm_num)
    · obtain ⟨V, hVn, hY, hdvd, -⟩ := hD.dvd_of_isExt hB pow_of_isExtraspecial2
      exact hD.false_of_dvd (Vol2.Ch11.SecB.card_isPSL_three_two_one hY ▸ hdvd) (by norm_num)
    · obtain ⟨V, hVn, hY, hdvd, -⟩ := hD.dvd_of_isExt hB pow_of_isE2
      exact hD.false_of_dvd (card_hat_six hY ▸ hdvd) (by norm_num)
  ·
    exact (hD.false_of_card (card_alt_five h.1) (by norm_num)).elim
  ·
    obtain ⟨V, hVn, hY, hdvd, -⟩ := hD.dvd_of_isExt h.1 pow_of_isExtraspecial2
    exact (hD.false_of_dvd (card_alt_five hY ▸ hdvd) (by norm_num)).elim
  ·
    exfalso
    obtain ⟨-, hB⟩ := h
    rcases hB with hB | hB | hB | hB | hB | hB
    ·
      obtain ⟨V, hVn, hY, -, m, hm⟩ := hD.dvd_of_isExt hB pow_of_isExtraspecial2
      rw [card_hat_M22 hY] at hm
      have := hD.odd_part (e := m + 7) (m := 10395) (by decide)
        (by rw [hm, pow_add]; ring)
      omega
    ·
      obtain ⟨V, hVn, hY, -, m, hm⟩ := hD.dvd_of_isExt hB pow_of_isE2
      rw [card_isSporadic_M24 hY] at hm
      have := hD.odd_part (e := m + 10) (m := 239085) (by decide)
        (by rw [hm, pow_add]; ring)
      omega
    · exact hD.false_of_eq (hD.cardQ.symm.trans (card_alt_five hB)) (by norm_num)
    · exact hD.false_of_eq (hD.cardQ.symm.trans (card_hat_six hB)) (by norm_num)
    · exact hD.false_of_eq (hD.cardQ.symm.trans (card_isPSL_four_two_one hB)) (by norm_num)
    · exact hD.false_of_eq (hD.cardQ.symm.trans (Vol2.Ch11.SecB.card_isPSL_three_two_one hB))
        (by norm_num)
  ·
    exfalso
    obtain ⟨hB, -⟩ := h
    rcases hB with hB | hB
    · obtain ⟨V, hVn, hY, hdvd, -⟩ := hD.dvd_of_isExt hB
        (fun V _ _ h => Vol2.Ch11.SecA.card_isZ4StarExtra2 h)
      exact hD.false_of_dvd (card_alt_five hY ▸ hdvd) (by norm_num)
    · obtain ⟨V, hVn, hY, hdvd, -⟩ := hD.dvd_of_isExt hB
        (fun V _ _ h => ⟨6, Vol2.Ch11.SecA.card_isZ4Cubed h⟩)
      exact hD.false_of_dvd (Vol2.Ch11.SecB.card_isPSL_three_two_one hY ▸ hdvd) (by norm_num)
  ·
    exfalso
    obtain ⟨hB, -⟩ := h
    rcases hB with hB | hB
    · obtain ⟨V, hVn, hY, hdvd, -⟩ := hD.dvd_of_isExt hB pow_of_isExtraspecial2
      exact hD.false_of_dvd (Vol2.Ch11.SecB.card_isPSL_three_two_one hY ▸ hdvd) (by norm_num)
    · obtain ⟨V, hVn, hY, hdvd, -⟩ := hD.dvd_of_isExt hB pow_of_isE2
      exact hD.false_of_dvd (card_hat_six hY ▸ hdvd) (by norm_num)
  ·
    exfalso
    obtain ⟨hB, -, -⟩ := h
    rcases hB with hB | hB
    · exact hD.false_of_eq (hD.cardQ.symm.trans (card_alt_five hB)) (by norm_num)
    · exact hD.false_of_eq (hD.cardQ.symm.trans (Vol2.Ch11.SecB.card_isPSL_three_two_one hB))
        (by norm_num)

end Data513

@[expose] def IsA7J2M23 (Y : Type) [Group Y] : Prop :=
  Nonempty (Y ≃* alternatingGroup (Fin 7)) ∨ Nonempty (Y ≃* NativeSporadic.J2) ∨
    Nonempty (Y ≃* NativeSporadic.M23)

namespace IsA7J2M23

variable {Y Y' : Type} [Group Y] [Group Y']

theorem card
    (h : IsA7J2M23 Y) :
    Nat.card Y = 2520 ∨ Nat.card Y = 604800 ∨ Nat.card Y = 10200960 := by
  rcases h with h | h | h
  · exact Or.inl (card_alt_seven h)
  · obtain ⟨f⟩ := h
    refine Or.inr (Or.inl ?_)
    rw [Nat.card_congr f.toEquiv]
    exact CFSG.Sporadic.J2.card_J2
  · obtain ⟨f⟩ := h
    refine Or.inr (Or.inr ?_)
    rw [Nat.card_congr f.toEquiv, CFSG.Sporadic.Mathieu.nativeM23_eq]
    exact (Nat.card_eq_fintype_card (α := CFSG.M23.M23Group.H0)).trans
      CFSG.M23.M23Group.card_M23

theorem isSimpleGroup
    (h : IsA7J2M23 Y) : IsSimpleGroup Y := by
  rcases h with h | h | h
  · obtain ⟨f⟩ := h
    exact (MulEquiv.isSimpleGroup_congr f).mpr (alternatingGroup.isSimpleGroup (by norm_num))
  · obtain ⟨f⟩ := h
    exact (MulEquiv.isSimpleGroup_congr f).mpr CFSG.Sporadic.J2.isSimpleGroup_J2
  · obtain ⟨f⟩ := h
    exact (MulEquiv.isSimpleGroup_congr f).mpr CFSG.Sporadic.Mathieu.fam_m23_simplicity.2.2

theorem alt_of_card
    (h : IsA7J2M23 Y) (hc : Nat.card Y = 2520) : Nonempty (Y ≃* alternatingGroup (Fin 7)) := by
  rcases h with h | h | h
  · exact h
  · obtain ⟨f⟩ := h
    have hJ : Nat.card Y = 604800 := by
      rw [Nat.card_congr f.toEquiv]
      exact CFSG.Sporadic.J2.card_J2
    omega
  · obtain ⟨f⟩ := h
    have hM : Nat.card Y = 10200960 := by
      rw [Nat.card_congr f.toEquiv, CFSG.Sporadic.Mathieu.nativeM23_eq]
      exact (Nat.card_eq_fintype_card (α := CFSG.M23.M23Group.H0)).trans
        CFSG.M23.M23Group.card_M23
    omega

end IsA7J2M23

section Compare

variable {G : Type} [Group G] [Finite G]

theorem eq_of_modO2Image_eq {X A B : Subgroup G} (hBX : B ≤ X) (hAB : A ≤ B) (hB : ⁅B, B⁆ = B)
    (hPA : pCoreOf 2 X ≤ Subgroup.normalizer (A : Set G))
    (heq : modO2Image X A = modO2Image X B) : A = B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm hAB (le_of_perfect_of_le_sup hB ?_ (pCoreOf_isPGroup 2 X) hPA)
  intro b hb
  have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨b, hBX hb⟩ ∈ modO2Image X A := by
    rw [heq]
    exact ⟨⟨b, hBX hb⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩
  obtain ⟨y, hy, hyx⟩ := hmem
  have h1 : y⁻¹ * ⟨b, hBX hb⟩ ∈ CFSG.pCore 2 ↥X := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hyx
    exact hyx
  have h1' : y⁻¹ * ⟨b, hBX hb⟩ ∈ CFSG.Open.pCore 2 ↥X := by
    exact h1
  have hb' : b = (y : G) * ((y⁻¹ * ⟨b, hBX hb⟩ : ↥X) : G) := by simp
  rw [hb']
  exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hy))
    (Subgroup.mem_sup_right ⟨_, h1', rfl⟩)

theorem eq_or_alt_m23
    (hQ : CFSG.QuasithinUnique.quasithinIsQTKECat G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h312 : A312ForSQTK) {X T A B : Subgroup G}
    (hO : pCoreOf 2 X ≠ ⊥) (hS : IsSylowTwoOf T X) (hAX : A ≤ X) (hA : A ∈ lFamily T)
    (hB : B ∈ cComp X) (hAB : A ≤ B) (hTA : T ≤ Subgroup.normalizer (A : Set G))
    (hAl : IsA7J2M23 (O2Q A)) (hBl : IsA7J2M23 (O2Q B)) :
    A = B ∨ (Nonempty (O2Q A ≃* alternatingGroup (Fin 7)) ∧
      Nonempty (O2Q B ≃* NativeSporadic.M23)) := by
  obtain ⟨eB⟩ := modO2_mulEquiv hB
  rcases lemma_1_2_4_list hQ hs hnab h312 hO hS hAX hA hB hAB with hbar | hcase | hnq
  · exact Or.inl (eq_of_modO2Image_eq (le_of_mem_cComp hB) hAB hB.2.1
      ((F7.isSylowTwoOf_pCoreOf_le hS).trans hTA) hbar)
  · right
    obtain ⟨eA⟩ := Vol2.Ch11.SecA.modO2Image_quotEquiv hAX
    have hc : Nat.card (ModO2 (modO2Image X A)) = Nat.card (O2Q A) :=
      (Nat.card_congr eA.toEquiv).symm
    obtain ⟨h2520, ⟨eM⟩⟩ := (data513_of (hc ▸ hAl.card) rfl).of_case hcase
    exact ⟨hAl.alt_of_card (hc ▸ h2520), ⟨eB.trans eM⟩⟩
  · exfalso
    apply A312.not_quasisimple_of_nonquasi hnq
    have : IsSimpleGroup (O2Q B) := hBl.isSimpleGroup
    have : IsSimpleGroup ↥(modO2Image X B) := (MulEquiv.isSimpleGroup_congr eB).mp this
    have : Group.IsPerfect ↥B := Subgroup.isPerfect_iff.mpr hB.2.1
    have : Group.IsPerfect ↥(modO2Image X B) :=
      Group.IsPerfect.ofSurjective (barMap_surjective (le_of_mem_cComp hB))
    exact isQuasisimple_of_isSimpleGroup_of_isPerfect

end Compare

end CFSG.Quasithin.H13
