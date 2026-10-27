module

public import CFSG.Quasithin.Vol2.Ch11SecA11Cases1

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Blueprint

variable {Q : Type} [Group Q] [Finite Q] {B L : Subgroup Q} {n : ℕ}

theorem BarData.oSL2_eq_ext (hD : BarData B n) {PV PY : ∀ (V : Type) [Group V], Prop}
    (h : IsExt ↥B PV PY)
    (hPV : ∀ (V : Type) [Group V] [Finite V], PV V → ∃ k, Nat.card V = 2 ^ k) {d o : ℕ}
    (ho : Odd o) (hPY : ∀ (Y : Type) [Group Y], PY Y → Nat.card Y = 2 ^ d * o) :
    oSL2 n = o := by
  obtain ⟨V, _, hY, k, hk⟩ := card_of_isExt h hPV
  exact hD.oSL2_eq ho (card_ext_eq hk (hPY _ hY))

theorem card_alt5 {Y : Type} [Group Y] (h : IsAlt 5 Y) : Nat.card Y = 2 ^ 2 * 15 := by
  rw [card_of_isAlt (by norm_num) h]
  decide

theorem card_alt6 {Y : Type} [Group Y] (h : IsAlt 6 Y) : Nat.card Y = 2 ^ 3 * 45 := by
  rw [card_of_isAlt (by norm_num) h]
  decide

theorem card_alt7 {Y : Type} [Group Y] (h : IsAlt 7 Y) : Nat.card Y = 2 ^ 3 * 315 := by
  rw [card_of_isAlt (by norm_num) h]
  decide

theorem card_hat6 {Y : Type} [Group Y] (h : IsHat Y (alternatingGroup (Fin 6))) :
    Nat.card Y = 2 ^ 3 * 135 := by
  rw [card_of_isHat h, nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem card_L32 {Y : Type} [Group Y] (h : IsPSL 3 2 1 Y) : Nat.card Y = 2 ^ 3 * 21 := by
  rw [card_of_isPSL (by norm_num) h]
  decide

theorem card_L42 {Y : Type} [Group Y] (h : IsPSL 4 2 1 Y) : Nat.card Y = 2 ^ 6 * 315 := by
  rw [card_of_isPSL (by norm_num) h]
  decide

theorem card_L34 {Y : Type} [Group Y] (h : IsPSL 3 2 2 Y) : Nat.card Y = 2 ^ 6 * 315 := by
  rw [card_of_isPSL (by norm_num) h]
  decide

omit [Finite Q] in
theorem concl_C10 (hD : BarData B n) (h : A312C10 B L) : Concl1111 ↥L n := by
  obtain ⟨p, hp, hp3, ⟨V, hV, ⟨e⟩, -⟩, -⟩ := h
  exfalso
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

omit [Finite Q] in
theorem concl_C11 (hD : BarData B n) (h : A312C11 B L) : Concl1111 ↥L n :=
  absurd (hD.oSL2_eq (by decide) (card_alt6 h.1)) oSL2_ne_45

theorem concl_C12 (hD : BarData B n) (h : A312C12 B L) : Concl1111 ↥L n := by
  have hE : ∀ (V : Type) [Group V] [Finite V], IsE2 4 V → ∃ k, Nat.card V = 2 ^ k :=
    fun V _ _ hV => ⟨4, card_isE2 hV⟩
  rcases h with ⟨hB | hB, hL⟩ | ⟨hB | hB, hL⟩
  · have := hD.oSL2_eq_ext hB hE (by decide) (fun Y _ hY => card_alt5 hY)
    exact Or.inr ⟨oSL2_eq_fifteen this, three_M22 hL⟩
  · exact absurd (hD.oSL2_eq_ext hB hE (by decide) (fun Y _ hY => card_alt6 hY)) oSL2_ne_45
  · have := hD.oSL2_eq_ext hB hE (by decide) (fun Y _ hY => card_alt5 hY)
    exact Or.inr ⟨oSL2_eq_fifteen this, three_hatM22 hL⟩
  · exact absurd (hD.oSL2_eq_ext hB hE (by decide) (fun Y _ hY => card_hat6 hY)) oSL2_ne_135

theorem concl_C13 (hD : BarData B n) (h : A312C13 B L) : Concl1111 ↥L n := by
  have hE : ∀ m, ∀ (V : Type) [Group V] [Finite V], IsE2 m V → ∃ k, Nat.card V = 2 ^ k :=
    fun m V _ _ hV => ⟨m, card_isE2 hV⟩
  rcases h with ⟨hB | hB | hB | hB | hB | hB | hB, hL⟩
  · obtain ⟨e⟩ := hB
    exact (hD.false_of_M22 (k := 0) (m := 1) (one_dvd 3)
      (by rw [Nat.card_congr e.toEquiv, pow_zero, one_mul, one_mul]; rfl)).elim
  · exact absurd (hD.oSL2_eq (by decide) (card_L34 hB)) oSL2_ne_315
  · exact absurd (hD.oSL2_eq_ext hB (hE 4) (by decide) (fun Y _ hY => card_alt7 hY)) oSL2_ne_315
  · exact absurd (hD.oSL2_eq_ext hB (hE 4) (by decide) (fun Y _ hY => card_L32 hY)) oSL2_ne_21
  · exact absurd (hD.oSL2_eq_ext hB (hE 3) (by decide) (fun Y _ hY => card_L32 hY)) oSL2_ne_21
  · exact absurd (hD.oSL2_eq_ext hB (hE 4) (by decide) (fun Y _ hY => card_alt6 hY)) oSL2_ne_45
  · have := hD.oSL2_eq_ext hB (hE 4) (by decide) (fun Y _ hY => card_alt5 hY)
    exact Or.inr ⟨oSL2_eq_fifteen this, three_M23 hL⟩

theorem concl_C14 (hD : BarData B n) (h : A312C14 B L) : Concl1111 ↥L n := by
  have hE : ∀ m, ∀ (V : Type) [Group V] [Finite V], IsE2 m V → ∃ k, Nat.card V = 2 ^ k :=
    fun m V _ _ hV => ⟨m, card_isE2 hV⟩
  rcases h with ⟨hB | hB | hB | hB, -⟩
  · exact absurd (hD.oSL2_eq_ext hB (hE 4) (by decide) (fun Y _ hY => card_L42 hY)) oSL2_ne_315
  · exact absurd (hD.oSL2_eq_ext hB (hE 6) (by decide) (fun Y _ hY => card_L32 hY)) oSL2_ne_21
  · exact absurd (hD.oSL2_eq_ext hB (fun V _ _ hV => ⟨_, card_isExtraspecial2 hV⟩) (by decide)
      (fun Y _ hY => card_L32 hY)) oSL2_ne_21
  · exact absurd (hD.oSL2_eq_ext hB (hE 6) (by decide) (fun Y _ hY => card_hat6 hY)) oSL2_ne_135

omit [Finite Q] in
theorem concl_C15 (hD : BarData B n) (h : A312C15 B L) : Concl1111 ↥L n :=
  Or.inr ⟨hD.eq_two (card_alt5 h.1), three_J1 h.2⟩

theorem concl_C16 (hD : BarData B n) (h : A312C16 B L) : Concl1111 ↥L n := by
  have := hD.oSL2_eq_ext h.1 (fun V _ _ hV => ⟨_, card_isExtraspecial2 hV⟩) (by decide)
    (fun Y _ hY => card_alt5 hY)
  exact Or.inr ⟨oSL2_eq_fifteen this, three_J2 h.2⟩

theorem concl_C17 (hD : BarData B n) (h : A312C17 B L) : Concl1111 ↥L n := by
  rcases h with ⟨hL, hB | hB | hB | hB | hB | hB⟩
  · obtain ⟨V, _, hY, k, hk⟩ := card_of_isExt hB (fun V _ _ hV => ⟨_, card_isExtraspecial2 hV⟩)
    exact (hD.false_of_M22 (k := k) (m := 3) (dvd_refl 3)
      (by rw [hk, card_of_isHat hY, mul_comm _ 3]; rfl)).elim
  · obtain ⟨V, _, ⟨e⟩, k, hk⟩ := card_of_isExt hB (fun V _ _ hV => ⟨_, card_isE2 hV⟩)
    exact (hD.false_of_M24 (k := k) (by rw [hk, Nat.card_congr e.toEquiv]; rfl)).elim
  · exact Or.inr ⟨hD.eq_two' (card_alt5 hB), three_J4 hL⟩
  · exact absurd (hD.oSL2_eq' (by decide) (card_hat6 hB)) oSL2_ne_135
  · exact absurd (hD.oSL2_eq' (by decide) (card_L42 hB)) oSL2_ne_315
  · exact absurd (hD.oSL2_eq' (by decide) (card_L32 hB)) oSL2_ne_21

theorem concl_C18 (hD : BarData B n) (h : A312C18 B L) : Concl1111 ↥L n := by
  rcases h with ⟨hB | hB, hL⟩
  · have := hD.oSL2_eq_ext hB (fun V _ _ hV => card_isZ4StarExtra2 hV) (by decide)
      (fun Y _ hY => card_alt5 hY)
    exact Or.inr ⟨oSL2_eq_fifteen this, three_HS hL⟩
  · exact absurd (hD.oSL2_eq_ext hB (fun V _ _ hV => ⟨6, card_isZ4Cubed hV⟩) (by decide)
      (fun Y _ hY => card_L32 hY)) oSL2_ne_21

theorem concl_C19 (hD : BarData B n) (h : A312C19 B L) : Concl1111 ↥L n := by
  rcases h with ⟨hB | hB, -⟩
  · exact absurd (hD.oSL2_eq_ext hB (fun V _ _ hV => ⟨_, card_isExtraspecial2 hV⟩) (by decide)
      (fun Y _ hY => card_L32 hY)) oSL2_ne_21
  · exact absurd (hD.oSL2_eq_ext hB (fun V _ _ hV => ⟨6, card_isE2 hV⟩) (by decide)
      (fun Y _ hY => card_hat6 hY)) oSL2_ne_135

omit [Finite Q] in
theorem concl_C20 (hD : BarData B n) (h : A312C20 B L) : Concl1111 ↥L n := by
  rcases h with ⟨hB | hB, -, hL⟩
  · exact Or.inr ⟨hD.eq_two' (card_alt5 hB), three_Ru hL⟩
  · exact absurd (hD.oSL2_eq' (by decide) (card_L32 hB)) oSL2_ne_21

theorem concl_of_a312Case
    (hF : FactL2Parabolic) (hD : BarData B n) (h : A312Case B L) :
    Concl1111 ↥L n := by
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact concl_C2 hF hD h
  · exact concl_C3 hD h
  · exact concl_C4 hD h
  · exact concl_C5 hD h
  · exact concl_C6 hD h
  · exact concl_C7 hD h
  · exact concl_C8 hD h
  · exact concl_C9 hD h
  · exact concl_C10 hD h
  · exact concl_C11 hD h
  · exact concl_C12 hD h
  · exact concl_C13 hD h
  · exact concl_C14 hD h
  · exact concl_C15 hD h
  · exact concl_C16 hD h
  · exact concl_C17 hD h
  · exact concl_C18 hD h
  · exact concl_C19 hD h
  · exact concl_C20 hD h

end CFSG.Quasithin.Vol2.Ch11.SecA
