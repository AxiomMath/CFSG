module

public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Quasithin.Vol2.Ch11SecA11Cases2

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Vol2.Ch11.SecA CFSG.Blueprint

@[expose] def OutA5 (X : Type) [Group X] : Prop :=
  (IsAlt 7 X ∨ IsHat X ↥(alternatingGroup (Fin 7))) ∨ IsPSL 2 5 2 X ∨
    (∃ p : ℕ, p.Prime ∧ (p % 5 = 1 ∨ p % 5 = 4) ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧ IsPSL 2 p 1 X) ∨
    IsSporadic .J1 X ∨ IsSporadic .J4 X

@[expose] def OutE16 (X : Type) [Group X] : Prop :=
  IsSporadic .M22 X ∨ IsHat X (NativeSporadic.Carrier .M22) ∨ IsSporadic .M23 X ∨
    IsSporadic .J4 X

variable {Q : Type} [Group Q] [Finite Q] {B L : Subgroup Q} {n : ℕ}

omit [Finite Q] in
theorem card_cases_two
    (hT : (Nat.card ↥B = 2 ^ (3 * n) * oSL2 n ∧ Nat.card ↥(CFSG.pCore 2 ↥B) = 2 ^ (2 * n)) ∨
      (Nat.card ↥B = 2 ^ n * oSL2 n ∧ Nat.card ↥(CFSG.pCore 2 ↥B) = 1)) (hn : n = 2) :
    (Nat.card ↥B = 960 ∧ Nat.card ↥(CFSG.pCore 2 ↥B) = 16) ∨
      (Nat.card ↥B = 60 ∧ Nat.card ↥(CFSG.pCore 2 ↥B) = 1) := by
  subst hn
  rcases hT with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨by rw [h1]; rfl, by rw [h2]; rfl⟩
  · exact Or.inr ⟨by rw [h1]; rfl, h2⟩

omit [Finite Q] in
theorem card_ext {PV PY : ∀ (V : Type) [Group V], Prop} (h : IsExt ↥B PV PY) :
    ∃ (V : Subgroup ↥B) (_ : V.Normal), PV ↥V ∧ PY (↥B ⧸ V) ∧
      Nat.card ↥B = Nat.card ↥V * Nat.card (↥B ⧸ V) := by
  obtain ⟨V, hV, hPV, hPY⟩ := h
  exact ⟨V, hV, hPV, hPY, by rw [V.card_eq_card_quotient_mul_card_subgroup, mul_comm]⟩

theorem card_ext_E16_A5 (h : IsExt ↥B (fun V _ => IsE2 4 V) (fun Y _ => IsAlt 5 Y)) :
    Nat.card ↥B = 960 := by
  obtain ⟨V, _, hV, hY, hc⟩ := card_ext h
  rw [hc, card_isE2 hV, card_alt5 hY]
  norm_num

theorem rows_blk (hD : BarData B n) (h : A312Case B L)
    (hT : (Nat.card ↥B = 2 ^ (3 * n) * oSL2 n ∧ Nat.card ↥(CFSG.pCore 2 ↥B) = 2 ^ (2 * n)) ∨
      (Nat.card ↥B = 2 ^ n * oSL2 n ∧ Nat.card ↥(CFSG.pCore 2 ↥B) = 1)) :
    A312C2 B L ∨ (n = 2 ∧ ((Nat.card ↥B = 60 ∧ OutA5 ↥L) ∨ (Nat.card ↥B = 960 ∧ OutE16 ↥L))) := by
  have hE : ∀ m, ∀ (V : Type) [Group V] [Finite V], IsE2 m V → ∃ k, Nat.card V = 2 ^ k :=
    fun m _ _ _ hV => ⟨m, card_isE2 hV⟩
  have hX : ∀ (V : Type) [Group V] [Finite V], ∀ m, IsExtraspecial2 m V →
      ∃ k, Nat.card V = 2 ^ k := fun V _ _ m hV => ⟨_, card_isExtraspecial2 hV⟩
  have hc2 := card_cases_two hT
  rcases h with h | ⟨f, hf, -⟩ | ⟨hB, -⟩ | ⟨hB, -⟩ | ⟨hB | hB, hL⟩ | (⟨hB, -⟩ | ⟨hB, -⟩) | h | h |
      h | h | h | h | h | h | h | h | h | h | h
  · exact Or.inl h
  · exfalso
    apply not_three_dvd_card_of_isSz hf
    rw [hD.cardQ]
    exact dvd_mul_of_dvd_right (three_dvd_oSL2 n) _
  · exact absurd (hD.oSL2_eq' (d := 3) (by decide)
      (by rw [card_of_isPSL (by norm_num) hB]; decide)) oSL2_ne_21
  · exact absurd (hD.oSL2_eq' (d := 6) (by decide)
      (by rw [card_of_isPSL (by norm_num) hB]; decide)) oSL2_ne_315
  · exact Or.inr ⟨hD.eq_two (card_alt5 hB), Or.inl ⟨by rw [card_alt5 hB]; norm_num, Or.inl hL⟩⟩
  · exact absurd (hD.oSL2_eq (by decide) (card_L32 hB)) oSL2_ne_21
  · exact absurd (hD.oSL2_eq (by decide) (card_alt6 hB)) oSL2_ne_45
  · exact absurd (hD.oSL2_eq (by decide) (card_hat6 hB)) oSL2_ne_135
  ·
    rcases h with ⟨p, hp, hp3, hB, hL⟩ | ⟨hB, p, hp, hL, hp5, hp8⟩
    · have h2 := two_mul_card_of_isPSL_two hp (by omega) hB
      obtain ⟨a, ha⟩ := hD.card
      obtain ⟨rfl, hn⟩ := eq_five_of_sl2 hp (by omega) hD.two_le (b := a + n + 1) (by omega)
        (by rw [← h2, ha, pow_succ]; ring)
      exact Or.inr ⟨hn, Or.inl ⟨by omega, Or.inr (Or.inl hL)⟩⟩
    · exact Or.inr ⟨hD.eq_two (card_alt5 hB), Or.inl ⟨by rw [card_alt5 hB]; norm_num,
        Or.inr (Or.inr (Or.inl ⟨p, hp, mod_five_of_sq hp5, hp8, hL⟩))⟩⟩
  ·
    exfalso
    rcases h with ⟨s, p, hp, hp3, hB, hL⟩ | ⟨hB, -⟩ | ⟨hB, -⟩
    · obtain ⟨a, ha⟩ := hD.card
      obtain ⟨rfl, hn⟩ := eq_five_of_sl2 hp (by omega) hD.two_le (b := a + n) (by omega)
        (by rw [← card_of_isSL2 hp hB, ha])
      have hc := card_of_isSL2 hp hB
      rcases hc2 hn with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
    · exact absurd (hD.oSL2_eq (by decide) (card_alt6 hB)) oSL2_ne_45
    · exact absurd (hD.oSL2_eq (by decide) (card_hat6 hB)) oSL2_ne_135
  ·
    exfalso
    obtain ⟨p, hp, hp3, ⟨V, hV, ⟨e⟩, -⟩, -⟩ := h
    have : NeZero p := ⟨hp.ne_zero⟩
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
  · exact absurd (hD.oSL2_eq (by decide) (card_alt6 h.1)) oSL2_ne_45
  ·
    rcases h with ⟨hB | hB, hL⟩ | ⟨hB | hB, hL⟩
    · exact Or.inr ⟨oSL2_eq_fifteen (hD.oSL2_eq_ext hB (hE 4) (by decide)
        (fun Y _ hY => card_alt5 hY)), Or.inr ⟨card_ext_E16_A5 hB, Or.inl hL⟩⟩
    · exact absurd (hD.oSL2_eq_ext hB (hE 4) (by decide) (fun Y _ hY => card_alt6 hY))
        oSL2_ne_45
    · exact Or.inr ⟨oSL2_eq_fifteen (hD.oSL2_eq_ext hB (hE 4) (by decide)
        (fun Y _ hY => card_alt5 hY)), Or.inr ⟨card_ext_E16_A5 hB, Or.inr (Or.inl hL)⟩⟩
    · exact absurd (hD.oSL2_eq_ext hB (hE 4) (by decide) (fun Y _ hY => card_hat6 hY))
        oSL2_ne_135
  ·
    rcases h with ⟨⟨⟨e⟩⟩ | hB | hB | hB | hB | hB | hB, hL⟩
    · exact (hD.false_of_M22 (k := 0) (m := 1) (one_dvd 3)
        (by rw [Nat.card_congr e.toEquiv, pow_zero, one_mul, one_mul]; rfl)).elim
    · exact absurd (hD.oSL2_eq (by decide) (card_L34 hB)) oSL2_ne_315
    · exact absurd (hD.oSL2_eq_ext hB (hE 4) (by decide)
        (fun Y _ hY => Ch11.SecA.card_alt7 hY)) oSL2_ne_315
    · exact absurd (hD.oSL2_eq_ext hB (hE 4) (by decide) (fun Y _ hY => card_L32 hY))
        oSL2_ne_21
    · exact absurd (hD.oSL2_eq_ext hB (hE 3) (by decide) (fun Y _ hY => card_L32 hY))
        oSL2_ne_21
    · exact absurd (hD.oSL2_eq_ext hB (hE 4) (by decide) (fun Y _ hY => card_alt6 hY))
        oSL2_ne_45
    · exact Or.inr ⟨oSL2_eq_fifteen (hD.oSL2_eq_ext hB (hE 4) (by decide)
        (fun Y _ hY => card_alt5 hY)), Or.inr ⟨card_ext_E16_A5 hB, Or.inr (Or.inr (Or.inl hL))⟩⟩
  ·
    exfalso
    rcases h with ⟨hB | hB | hB | hB, -⟩
    · exact oSL2_ne_315 (hD.oSL2_eq_ext hB (hE 4) (by decide) (fun Y _ hY => card_L42 hY))
    · exact oSL2_ne_21 (hD.oSL2_eq_ext hB (hE 6) (by decide) (fun Y _ hY => card_L32 hY))
    · exact oSL2_ne_21 (hD.oSL2_eq_ext hB (fun V _ _ hV => hX V _ hV) (by decide)
        (fun Y _ hY => card_L32 hY))
    · exact oSL2_ne_135 (hD.oSL2_eq_ext hB (hE 6) (by decide) (fun Y _ hY => card_hat6 hY))
  · exact Or.inr ⟨hD.eq_two (card_alt5 h.1), Or.inl ⟨by rw [card_alt5 h.1]; norm_num,
      Or.inr (Or.inr (Or.inr (Or.inl h.2)))⟩⟩
  ·
    exfalso
    have hn := oSL2_eq_fifteen (hD.oSL2_eq_ext h.1 (fun V _ _ hV => hX V _ hV) (by decide)
      (fun Y _ hY => card_alt5 hY))
    obtain ⟨V, _, hV, hY, hc⟩ := card_ext h.1
    rw [card_isExtraspecial2 hV, card_alt5 hY] at hc
    rcases hc2 hn with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
  ·
    rcases h with ⟨hL, hB | hB | hB | hB | hB | hB⟩
    · obtain ⟨V, _, hY, k, hk⟩ := card_of_isExt hB (fun V _ _ hV => hX V _ hV)
      exact (hD.false_of_M22 (k := k) (m := 3) (dvd_refl 3)
        (by rw [hk, card_of_isHat hY, mul_comm _ 3]; rfl)).elim
    · obtain ⟨V, _, ⟨e⟩, k, hk⟩ := card_of_isExt hB (hE 11)
      exact (hD.false_of_M24 (k := k) (by rw [hk, Nat.card_congr e.toEquiv]; rfl)).elim
    · have hn := hD.eq_two' (card_alt5 hB)
      refine Or.inr ⟨hn, ?_⟩
      rcases hc2 hn with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact Or.inr ⟨h1, Or.inr (Or.inr (Or.inr hL))⟩
      · exact Or.inl ⟨h1, Or.inr (Or.inr (Or.inr (Or.inr hL)))⟩
    · exact absurd (hD.oSL2_eq' (by decide) (card_hat6 hB)) oSL2_ne_135
    · exact absurd (hD.oSL2_eq' (by decide) (card_L42 hB)) oSL2_ne_315
    · exact absurd (hD.oSL2_eq' (by decide) (card_L32 hB)) oSL2_ne_21
  ·
    exfalso
    rcases h with ⟨hB | hB, -⟩
    · have hn := oSL2_eq_fifteen (hD.oSL2_eq_ext hB (fun V _ _ hV => card_isZ4StarExtra2 hV)
        (by decide) (fun Y _ hY => card_alt5 hY))
      obtain ⟨V, _, ⟨Z, E, hZ, -, hEx, -, -, -⟩, hY, hc⟩ := card_ext hB
      rw [card_alt5 hY] at hc
      have hE32 : Nat.card ↥E = 2 ^ 5 := card_isExtraspecial2 hEx
      have hle : Nat.card ↥E ≤ Nat.card ↥V := Subgroup.card_le_card_group E
      rcases hc2 hn with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
    · exact absurd (hD.oSL2_eq_ext hB (fun V _ _ hV => ⟨6, card_isZ4Cubed hV⟩) (by decide)
        (fun Y _ hY => card_L32 hY)) oSL2_ne_21
  ·
    exfalso
    rcases h with ⟨hB | hB, -⟩
    · exact oSL2_ne_21 (hD.oSL2_eq_ext hB (fun V _ _ hV => hX V _ hV) (by decide)
        (fun Y _ hY => card_L32 hY))
    · exact oSL2_ne_135 (hD.oSL2_eq_ext hB (hE 6) (by decide) (fun Y _ hY => card_hat6 hY))
  ·
    exfalso
    rcases h with ⟨hB | hB, hc, -⟩
    · rcases hc2 (hD.eq_two' (card_alt5 hB)) with ⟨-, h1⟩ | ⟨-, h1⟩ <;> omega
    · exact absurd (hD.oSL2_eq' (by decide) (card_L32 hB)) oSL2_ne_21

end CFSG.Quasithin.Vol2.Ch10.SecB.C10KH
