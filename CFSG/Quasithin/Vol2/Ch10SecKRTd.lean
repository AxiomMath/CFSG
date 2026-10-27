module

public import CFSG.Quasithin.Vol2.Ch10SecKIK2r
public import CFSG.Quasithin.Vol2.Ch10SecKIK4a

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.KRT

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Vol2.Ch11.SecA CFSG.Blueprint
open CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

variable {Q : Type} [Group Q] {B L : Subgroup Q} {n M : ℕ}

theorem rows_KF1 (hD : BarData B n) (h : A312Case B L) (hJ : B56Card M)
    (hc : Nat.card ↥L = M ∨ Nat.card ↥L = 3 * M) : A312C2 B L ∨ A312C6 B L := by
  have hbad : BadConc ↥L → False := false_of_badConc hJ hc
  rcases h with h | ⟨f, hf, -⟩ | ⟨hB, -⟩ | ⟨hB, -⟩ | h6 | (⟨hB, -⟩ | ⟨hB, -⟩) | h | h |
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
  · exact Or.inr h6
  · exact absurd (hD.oSL2_eq (by decide) (card_alt6 hB)) oSL2_ne_45
  · exact absurd (hD.oSL2_eq (by decide) (card_hat6 hB)) oSL2_ne_135
  ·
    exfalso
    rcases h with ⟨p, hp, hp3, hB, hL⟩ | ⟨-, p, hp, hL, hp5, hp8⟩
    · have h2 := two_mul_card_of_isPSL_two hp (by omega) hB
      obtain ⟨a, ha⟩ := hD.card
      obtain ⟨rfl, -⟩ := eq_five_of_sl2 hp (by omega) hD.two_le (b := a + n + 1) (by omega)
        (by rw [← h2, ha, pow_succ]; ring)
      exact hbad (Or.inl hL)
    · exact false_of_psl2p hJ hc hp (mod_five_of_sq hp5) hp8 hL
  ·
    exfalso
    rcases h with ⟨s, p, hp, hp3, hB, hL⟩ | ⟨hB, -⟩ | ⟨hB, -⟩
    · obtain ⟨a, ha⟩ := hD.card
      obtain ⟨rfl, -⟩ := eq_five_of_sl2 hp (by omega) hD.two_le (b := a + n) (by omega)
        (by rw [← card_of_isSL2 hp hB, ha])
      exact hbad (Or.inr (Or.inr (Or.inl ⟨s, hL⟩)))
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
    exfalso
    rcases h with ⟨-, hL⟩ | ⟨-, hL⟩
    · exact hbad (by (iterate 4 right); exact Or.inl hL)
    · exact hbad (by (iterate 5 right); exact Or.inl hL)
  · exact (hbad (by (iterate 6 right); exact Or.inl h.2)).elim
  · exact (hbad (by (iterate 7 right); exact Or.inl h.2)).elim
  · exact (hbad (by (iterate 8 right); exact Or.inl h.2)).elim
  · exact (hbad (by (iterate 9 right); exact Or.inl h.2)).elim
  · exact (hbad (by (iterate 10 right); exact Or.inl h.1)).elim
  · exact (hbad (by (iterate 11 right); exact Or.inl h.2)).elim
  · exact (hbad (by (iterate 12 right); exact Or.inl h.2)).elim
  · exact (hbad (by (iterate 13 right); exact h.2.2)).elim

end CFSG.Quasithin.Vol2.Ch10.SecB.KRT
