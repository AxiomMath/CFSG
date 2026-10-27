module

public import CFSG.Quasithin.Vol2.Ch11SecSZK2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecA

variable {Q : Type} [Group Q] [Finite Q] {B L : Subgroup Q}

theorem L34Data.of_C12_C20 (hD : L34Data B) (hNot : FactL34NotL42)
    (h : A312C12 B L ∨ A312C13 B L ∨ A312C14 B L ∨ A312C15 B L ∨ A312C16 B L ∨ A312C17 B L ∨
      A312C18 B L ∨ A312C19 B L ∨ A312C20 B L) : IsSporadic .M23 ↥L := by
  have hE : ∀ m, ∀ (V : Type) [Group V] [Finite V], IsE2 m V → ∃ k, Nat.card V = 2 ^ k :=
    fun m V _ _ hV => ⟨m, card_isE2 hV⟩
  have hX : ∀ (V : Type) [Group V] [Finite V], ∀ {m : ℕ}, IsExtraspecial2 m V →
      ∃ k, Nat.card V = 2 ^ k := fun V _ _ _ hV => ⟨_, card_isExtraspecial2 hV⟩
  have h3 : Nat.card (ModO2 B) = 2 ^ 6 * 315 := card_L34 hD.psl
  rcases h with (⟨hB | hB, -⟩ | ⟨hB | hB, -⟩) | h | h | ⟨hB, -⟩ | ⟨hB, -⟩ | h | ⟨hB | hB, -⟩ |
      ⟨hB | hB, -⟩ | ⟨hB | hB, -, -⟩
  · exact (hD.false_of_ext_lt hB (hE 4) fun Y _ hY => by rw [card_alt5 hY]; norm_num).elim
  · exact (hD.false_of_ext_lt hB (hE 4) fun Y _ hY => by rw [card_alt6 hY]; norm_num).elim
  · exact (hD.false_of_ext_lt hB (hE 4) fun Y _ hY => by rw [card_alt5 hY]; norm_num).elim
  · exact (hD.false_of_ext_lt hB (hE 4) fun Y _ hY => by rw [card_hat6 hY]; norm_num).elim
  · obtain ⟨hB | hB | hB | hB | hB | hB | hB, hL⟩ := h
    · obtain ⟨e⟩ := hB
      exact (hD.not_prime_dvd (p := 11) (by norm_num) (by norm_num) (by norm_num)
        (by rw [Nat.card_congr e.toEquiv]; exact eleven_dvd_card_M22)).elim
    · exact hL
    · exact (hD.false_of_ext_lt hB (hE 4) fun Y _ hY => by rw [card_alt7 hY]; norm_num).elim
    · exact (hD.false_of_ext_lt hB (hE 4) fun Y _ hY => by rw [card_L32 hY]; norm_num).elim
    · exact (hD.false_of_ext_lt hB (hE 3) fun Y _ hY => by rw [card_L32 hY]; norm_num).elim
    · exact (hD.false_of_ext_lt hB (hE 4) fun Y _ hY => by rw [card_alt6 hY]; norm_num).elim
    · exact (hD.false_of_ext_lt hB (hE 4) fun Y _ hY => by rw [card_alt5 hY]; norm_num).elim
  · obtain ⟨hB | hB | hB | hB, -⟩ := h
    · exact (hD.false_of_ext_L42 hNot hB (hE 4)).elim
    · exact (hD.false_of_ext_lt hB (hE 6) fun Y _ hY => by rw [card_L32 hY]; norm_num).elim
    · exact (hD.false_of_ext_lt hB (fun V _ _ hV => hX V hV)
        fun Y _ hY => by rw [card_L32 hY]; norm_num).elim
    · exact (hD.false_of_ext_lt hB (hE 6) fun Y _ hY => by rw [card_hat6 hY]; norm_num).elim
  · exact (hD.false_of_lt (by rw [card_alt5 hB]; norm_num)).elim
  · exact (hD.false_of_ext_lt hB (fun V _ _ hV => hX V hV)
      fun Y _ hY => by rw [card_alt5 hY]; norm_num).elim
  · obtain ⟨-, hB | hB | hB | hB | hB | hB⟩ := h
    · exact (hD.false_of_ext_dvd hB (fun V _ _ hV => hX V hV) (p := 11) (by norm_num)
        (by norm_num) (by norm_num)
        fun Y _ hY => by
          rw [card_of_isHat hY]
          exact dvd_mul_of_dvd_left eleven_dvd_card_M22 3).elim
    · exact (hD.false_of_ext_dvd hB (hE 11) (p := 23) (by norm_num) (by norm_num) (by norm_num)
        fun Y _ hY => by
          obtain ⟨e⟩ := hY
          rw [Nat.card_congr e.toEquiv]
          exact twentythree_dvd_card_M24).elim
    · rw [card_alt5 hB] at h3
      norm_num at h3
    · rw [card_hat6 hB] at h3
      norm_num at h3
    · exact (hNot _ hD.psl hB).elim
    · rw [card_L32 hB] at h3
      norm_num at h3
  · exact (hD.false_of_ext_lt hB (fun V _ _ hV => card_isZ4StarExtra2 hV)
      fun Y _ hY => by rw [card_alt5 hY]; norm_num).elim
  · exact (hD.false_of_ext_lt hB (fun V _ _ hV => ⟨6, card_isZ4Cubed hV⟩)
      fun Y _ hY => by rw [card_L32 hY]; norm_num).elim
  · exact (hD.false_of_ext_lt hB (fun V _ _ hV => hX V hV)
      fun Y _ hY => by rw [card_L32 hY]; norm_num).elim
  · exact (hD.false_of_ext_lt hB (hE 6) fun Y _ hY => by rw [card_hat6 hY]; norm_num).elim
  · rw [card_alt5 hB] at h3
    norm_num at h3
  · rw [card_L32 hB] at h3
    norm_num at h3

theorem L34Data.of_a312Case
    (hD : L34Data B) (hNot : FactL34NotL42) (h : A312Case B L) :
    IsSporadic .M23 ↥L := by
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · exact (hD.false_C2_C11 hNot (Or.inl h)).elim
  · exact (hD.false_C2_C11 hNot (Or.inr (Or.inl h))).elim
  · exact (hD.false_C2_C11 hNot (Or.inr (Or.inr (Or.inl h)))).elim
  · exact (hD.false_C2_C11 hNot (Or.inr (Or.inr (Or.inr (Or.inl h))))).elim
  · exact (hD.false_C2_C11 hNot (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))).elim
  · exact (hD.false_C2_C11 hNot (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))).elim
  · exact (hD.false_C2_C11 hNot
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))).elim
  · exact (hD.false_C2_C11 hNot
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))).elim
  · exact (hD.false_C2_C11 hNot
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))).elim
  · exact (hD.false_C2_C11 hNot
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))).elim
  · exact hD.of_C12_C20 hNot h

end CFSG.Quasithin.Vol2.Ch11.SecS
