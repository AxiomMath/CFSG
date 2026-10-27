module

public import CFSG.Quasithin.Vol2.Ch11SecA11Concl
import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Quasithin.Vol2.Ch11SecA11Ord

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

section Orders

variable {X : Type} [Group X]

theorem card_of_isPSL_two_two {m : ℕ} (h : IsPSL 2 2 m X) :
    1 ≤ m ∧ Nat.card X = 2 ^ m * oSL2 m := by
  have hm : 1 ≤ m := h.1.2.1
  refine ⟨hm, ?_⟩
  rw [card_of_isPSL (by norm_num) h]
  have hg : Nat.gcd 2 (2 ^ m - 1) = 1 := Nat.coprime_two_left.mpr (odd_two_pow_sub_one hm)
  rw [hg, Nat.div_one]
  simp [oSL2, ← pow_mul, mul_comm]

theorem two_mul_card_of_isPSL_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : IsPSL 2 p 1 X) :
    2 * Nat.card X = p * (p ^ 2 - 1) :=
  CFSG.Open.StatedAPI.two_mul_card_of_statedClassicalModel_psl_two_prime hp hp2 h

theorem three_dvd_oSL2 (n : ℕ) : 3 ∣ oSL2 n := by
  have := Nat.sub_dvd_pow_sub_pow 4 1 n
  rwa [one_pow, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul] at this

end Orders

variable {Q : Type} [Group Q] {B L : Subgroup Q} {n : ℕ}

theorem concl_C2 [Finite Q] (hF : FactL2Parabolic) (hD : BarData B n) (h : A312C2 B L) :
    Concl1111 ↥L n := by
  obtain ⟨⟨m, hm⟩, hrk, P, hP, rfl⟩ := h
  obtain ⟨hm1, hcard⟩ := card_of_isPSL_two_two hm
  have hmn : m = n := eq_of_two_pow_mul_odd (odd_oSL2 hm1)
    (odd_oSL2 (m := n) (by have := hD.two_le; omega)) (hcard.symm.trans hD.cardQ)
  subst hmn
  exact Or.inl (hF Q L P m hD.two_le hrk hP hm)

theorem concl_C3
    (hD : BarData B n) (h : A312C3 B L) : Concl1111 ↥L n := by
  obtain ⟨f, hf, -⟩ := h
  exfalso
  apply not_three_dvd_card_of_isSz hf
  rw [hD.cardQ]
  exact dvd_mul_of_dvd_right (three_dvd_oSL2 n) _

theorem concl_C4 (hD : BarData B n) (h : A312C4 B L) : Concl1111 ↥L n := by
  obtain ⟨hB, -⟩ := h
  exact absurd (hD.oSL2_eq' (d := 3) (by decide)
    (by rw [card_of_isPSL (by norm_num) hB]; decide)) oSL2_ne_21

theorem concl_C5 (hD : BarData B n) (h : A312C5 B L) : Concl1111 ↥L n := by
  obtain ⟨hB, -⟩ := h
  exact absurd (hD.oSL2_eq' (d := 6) (by decide)
    (by rw [card_of_isPSL (by norm_num) hB]; decide)) oSL2_ne_315

theorem concl_C6 (hD : BarData B n) (h : A312C6 B L) : Concl1111 ↥L n := by
  obtain ⟨hB | hB, hL⟩ := h
  · have hn : n = 2 := hD.eq_two (d := 2) (by rw [card_of_isAlt (by norm_num) hB]; decide)
    exact Or.inr ⟨hn, hL.elim three_alt7 three_hat7⟩
  · exact absurd (hD.oSL2_eq (d := 3) (by decide)
      (by rw [card_of_isPSL (by norm_num) hB]; decide)) oSL2_ne_21

theorem concl_C7 (hD : BarData B n) (h : A312C7 B L) : Concl1111 ↥L n := by
  rcases h with ⟨hB, -⟩ | ⟨hB, -⟩
  · exact absurd (hD.oSL2_eq (d := 3) (by decide)
      (by rw [card_of_isAlt (by norm_num) hB]; decide)) oSL2_ne_45
  · exact absurd (hD.oSL2_eq (d := 3) (by decide)
      (by rw [card_of_isHat hB, nat_card_alternatingGroup, Nat.card_fin]; decide)) oSL2_ne_135

theorem concl_C8 (hD : BarData B n) (h : A312C8 B L) : Concl1111 ↥L n := by
  rcases h with ⟨p, hp, hp3, hB, hL⟩ | ⟨hB, p, hp, hL, hp5, hp8⟩
  · have h2 := two_mul_card_of_isPSL_two hp (by omega) hB
    obtain ⟨a, ha⟩ := hD.card
    obtain ⟨rfl, hn⟩ := eq_five_of_sl2 hp (by omega) hD.two_le (b := a + n + 1) (by omega)
      (by rw [← h2, ha, pow_succ]; ring)
    exact Or.inr ⟨hn, three_psl225 hL⟩
  · have hn : n = 2 := hD.eq_two (d := 2) (by rw [card_of_isAlt (by norm_num) hB]; decide)
    exact Or.inr ⟨hn, three_psl2p hp (mod_five_of_sq hp5) hp8 hL⟩

theorem concl_C9 (hD : BarData B n) (h : A312C9 B L) : Concl1111 ↥L n := by
  rcases h with ⟨s, p, hp, hp3, hB, hL⟩ | ⟨hB, -⟩ | ⟨hB, -⟩
  · obtain ⟨a, ha⟩ := hD.card
    obtain ⟨rfl, hn⟩ := eq_five_of_sl2 hp (by omega) hD.two_le (b := a + n) (by omega)
      (by rw [← card_of_isSL2 hp hB, ha])
    exact Or.inr ⟨hn, three_sl35 hL.symm⟩
  · exact absurd (hD.oSL2_eq (d := 3) (by decide)
      (by rw [card_of_isAlt (by norm_num) hB]; decide)) oSL2_ne_45
  · exact absurd (hD.oSL2_eq (d := 3) (by decide)
      (by rw [card_of_isHat hB, nat_card_alternatingGroup, Nat.card_fin]; decide)) oSL2_ne_135

end CFSG.Quasithin.Vol2.Ch11.SecA
