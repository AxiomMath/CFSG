module

public import CFSG.Quasithin.Vol2.Ch11SecSZK1
public import CFSG.Quasithin.Vol2.Ch11SecSFacts4

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecA

theorem eq_of_prime_dvd_315 {p : ℕ} (hp : p.Prime) (h : p ∣ 315) : p = 3 ∨ p = 5 ∨ p = 7 := by
  have h' : p ∣ 3 * (3 * (5 * 7)) := by norm_num; exact h
  rcases (Nat.Prime.dvd_mul hp).mp h' with h3 | h'
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3)
  rcases (Nat.Prime.dvd_mul hp).mp h' with h3 | h'
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3)
  rcases (Nat.Prime.dvd_mul hp).mp h' with h5 | h7
  · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h5))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h7))

theorem isPSL_of_mulEquiv {X Y : Type} [Group X] [Group Y] {n p f : ℕ} (e : X ≃* Y)
    (h : IsPSL n p f Y) : IsPSL n p f X := by
  obtain ⟨hadm, K, _, _, hK, ⟨e'⟩⟩ := h
  exact ⟨hadm, K, inferInstance, inferInstance, hK, ⟨e.trans e'⟩⟩

variable {Q : Type} [Group Q] [Finite Q] {B L : Subgroup Q}

omit [Finite Q] in
theorem L34Data.odd_eq' (hD : L34Data B) {d o : ℕ} (ho : Odd o)
    (h : Nat.card (ModO2 B) = 2 ^ d * o) : o = 315 := by
  rw [card_L34 hD.psl] at h
  have h2 := eq_of_two_pow_mul_odd (a := 6) (b := d) (by decide) ho h
  rw [← h2] at h
  exact (Nat.eq_of_mul_eq_mul_left (by positivity) h).symm

omit [Finite Q] in
theorem L34Data.false_of_lt (hD : L34Data B) (h : Nat.card ↥B < 2 ^ 6 * 315) : False :=
  absurd hD.le_card (not_le.mpr h)

omit [Finite Q] in
theorem L34Data.false_of_prime_dvd_card (hD : L34Data B) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpB : p ∣ Nat.card ↥B) (hsmall : p = 3 ∨ p = 5 ∨ p = 7 → False) : False := by
  by_cases h315 : p ∣ 315
  · exact hsmall (eq_of_prime_dvd_315 hp h315)
  · exact hD.not_prime_dvd hp hp2 h315 hpB

theorem L34Data.false_of_ext_lt (hD : L34Data B) {PV PY : ∀ (V : Type) [Group V], Prop}
    (h : IsExt ↥B PV PY)
    (hPV : ∀ (V : Type) [Group V] [Finite V], PV V → ∃ k, Nat.card V = 2 ^ k)
    (hY : ∀ (Y : Type) [Group Y], PY Y → Nat.card Y < 2 ^ 6 * 315) : False := by
  obtain ⟨V, _, hPY, -, hge, -⟩ := hD.ext h hPV
  exact absurd hge (not_le.mpr (hY _ hPY))

theorem L34Data.false_of_ext_dvd (hD : L34Data B) {PV PY : ∀ (V : Type) [Group V], Prop}
    (h : IsExt ↥B PV PY)
    (hPV : ∀ (V : Type) [Group V] [Finite V], PV V → ∃ k, Nat.card V = 2 ^ k) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hp315 : ¬ p ∣ 315)
    (hY : ∀ (Y : Type) [Group Y], PY Y → p ∣ Nat.card Y) : False := by
  obtain ⟨V, _, hPY, -⟩ := hD.ext h hPV
  refine hD.not_prime_dvd hp hp2 hp315 ((hY _ hPY).trans ?_)
  exact Dvd.intro _ V.card_eq_card_quotient_mul_card_subgroup.symm

theorem L34Data.false_of_ext_L42 (hD : L34Data B) (hNot : FactL34NotL42)
    {PV : ∀ (V : Type) [Group V], Prop} (h : IsExt ↥B PV (fun Y _ => IsPSL 4 2 1 Y))
    (hPV : ∀ (V : Type) [Group V] [Finite V], PV V → ∃ k, Nat.card V = 2 ^ k) : False := by
  obtain ⟨V, _, hY, hVO, -, -⟩ := hD.ext h hPV
  have hcY : Nat.card (↥B ⧸ V) = 2 ^ 6 * 315 := card_L42 hY
  have h1 := V.card_eq_card_quotient_mul_card_subgroup
  have h2 := (CFSG.pCore 2 ↥B).card_eq_card_quotient_mul_card_subgroup
  have h3 : Nat.card (↥B ⧸ CFSG.pCore 2 ↥B) = 2 ^ 6 * 315 := card_L34 hD.psl
  rw [hcY] at h1
  rw [h3] at h2
  have hVeq : V = CFSG.pCore 2 ↥B := Subgroup.eq_of_le_of_card_ge hVO (by
    have h4 : 2 ^ 6 * 315 * Nat.card ↥V = 2 ^ 6 * 315 * Nat.card ↥(CFSG.pCore 2 ↥B) := by
      rw [← h1, ← h2]
    exact (Nat.eq_of_mul_eq_mul_left (by norm_num) h4).symm.le)
  have e : ModO2 B ≃* ↥B ⧸ V := QuotientGroup.quotientMulEquivOfEq hVeq.symm
  exact hNot _ hD.psl (isPSL_of_mulEquiv e hY)

omit [Finite Q] in
theorem L34Data.false_C2_C11
    (hD : L34Data B) (hNot : FactL34NotL42)
    (h : A312C2 B L ∨ A312C3 B L ∨ A312C4 B L ∨ A312C5 B L ∨ A312C6 B L ∨ A312C7 B L ∨
      A312C8 B L ∨ A312C9 B L ∨ A312C10 B L ∨ A312C11 B L) : False := by
  have h3 : Nat.card (ModO2 B) = 2 ^ 6 * 315 := card_L34 hD.psl
  rcases h with ⟨⟨m, hm⟩, -⟩ | ⟨f, hf, -⟩ | ⟨hB, -⟩ | ⟨hB, -⟩ | ⟨hB | hB, -⟩ |
      (⟨hB, -⟩ | ⟨hB, -⟩) | (⟨p, hp, hp3, hB, -⟩ | ⟨hB, -⟩) |
      (⟨s, p, hp, hp3, hB, -⟩ | ⟨hB, -⟩ | ⟨hB, -⟩) | ⟨p, hp, hp3, ⟨V, hV, ⟨e⟩, -⟩, -⟩ | ⟨hB, -⟩
  · obtain ⟨hm1, hcard⟩ := card_of_isPSL_two_two hm
    exact absurd (hD.odd_eq' (odd_oSL2 hm1) hcard)
      (oSL2_ne (k := 6) (by decide) (by decide))
  · exact not_three_dvd_card_of_isSz hf (by rw [h3]; norm_num)
  · rw [card_L32 hB] at h3
    norm_num at h3
  · exact hNot _ hD.psl hB
  · exact hD.false_of_lt (by rw [card_alt5 hB]; norm_num)
  · exact hD.false_of_lt (by rw [card_L32 hB]; norm_num)
  · exact hD.false_of_lt (by rw [card_alt6 hB]; norm_num)
  · exact hD.false_of_lt (by rw [card_hat6 hB]; norm_num)
  · have h2 := two_mul_card_of_isPSL_two hp (by omega) hB
    have hpB : p ∣ Nat.card ↥B := by
      have h1 : p ∣ 2 * Nat.card ↥B := h2 ▸ dvd_mul_right p _
      exact ((Nat.coprime_primes hp Nat.prime_two).mpr (by omega)).dvd_of_dvd_mul_left h1
    refine hD.false_of_prime_dvd_card hp (by omega) hpB fun hp' => ?_
    have hle := hD.le_card
    rcases hp' with rfl | rfl | rfl <;> omega
  · exact hD.false_of_lt (by rw [card_alt5 hB]; norm_num)
  · have h2 := card_of_isSL2 hp hB
    have hpB : p ∣ Nat.card ↥B := h2 ▸ dvd_mul_right p _
    refine hD.false_of_prime_dvd_card hp (by omega) hpB fun hp' => ?_
    have hle := hD.le_card
    rcases hp' with rfl | rfl | rfl <;> omega
  · exact hD.false_of_lt (by rw [card_alt6 hB]; norm_num)
  · exact hD.false_of_lt (by rw [card_hat6 hB]; norm_num)
  · have : NeZero p := ⟨hp.ne_zero⟩
    have hcard : Nat.card ↥V = p ^ 2 := by
      rw [Nat.card_congr e.toEquiv]
      change Nat.card (Fin 2 → ZMod p) = p ^ 2
      rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    have hodd : Odd (Nat.card ↥V) := by
      rw [hcard]
      exact (hp.odd_of_ne_two (by omega)).pow
    have hbot := hD.odd V hV hodd
    rw [hbot, Subgroup.card_bot] at hcard
    have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  · exact hD.false_of_lt (by rw [card_alt6 hB]; norm_num)

end CFSG.Quasithin.Vol2.Ch11.SecS
