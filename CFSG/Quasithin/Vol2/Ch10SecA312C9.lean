module

public import CFSG.Quasithin.Vol2.Ch10SecA312C8

public section

namespace CFSG.Quasithin.Vol2.Ch10.A312C

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {X : Type} [Group X] {B : Subgroup X}

theorem case9 [Finite X] (hK : SylowTest X B) (hs : ¬ A312PairStructCase B)
    (h : A312C9 B ⊤) : False := by
  rcases h with ⟨s, p, hp, hp3, hB, hL⟩ | ⟨hB, hL⟩ | ⟨hB, hL⟩
  · have : Fact p.Prime := ⟨hp⟩
    have hBc := card_of_isSL2 hB
    cases s with
    | true =>
      rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd (p + 1) with ⟨j, hj⟩ | ⟨r, hr, hrd, hro⟩
      · exact hs (Or.inr (Or.inr (Or.inr (Or.inl ⟨true, p, hp, hp3, hB, hL, j, hj⟩))))
      · have hr2 : r ≠ 2 := by rintro rfl; exact (Nat.not_even_iff_odd.mpr hro) even_two
        refine hK r ((p + 1).factorization r) hr hr2
          ((hr.dvd_iff_one_le_factorization (by omega)).mp hrd) ?_ ?_
        · rw [hBc, sq_sub_one_eq]
          exact (Nat.ordProj_dvd _ _).trans ((dvd_mul_left _ _).mul_left _)
        · rw [← Subgroup.card_top]
          exact l3_not_dvd hp hr hr2 hrd hL
    | false =>
      rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd (p - 1) with ⟨j, hj⟩ | ⟨r, hr, hrd, hro⟩
      · exact hs (Or.inr (Or.inr (Or.inr (Or.inl ⟨false, p, hp, hp3, hB, hL, j, hj⟩))))
      · have hr2 : r ≠ 2 := by rintro rfl; exact (Nat.not_even_iff_odd.mpr hro) even_two
        refine hK r ((p - 1).factorization r) hr hr2
          ((hr.dvd_iff_one_le_factorization (by omega)).mp hrd) ?_ ?_
        · rw [hBc, sq_sub_one_eq]
          exact (Nat.ordProj_dvd _ _).trans ((dvd_mul_right _ _).mul_left _)
        · rw [← Subgroup.card_top]
          exact u3_not_dvd hr hr2 hrd hL
  · exact hK 3 2 Nat.prime_three (by norm_num) (by norm_num) (by rw [card_alt6 hB]; norm_num)
      (by rw [card_top_of (card_u35 hL)]; norm_num)
  · exact hK 3 3 Nat.prime_three (by norm_num) (by norm_num) (by rw [card_hat6 hB]; norm_num)
      (by rw [card_top_of (card_su35 hL)]; norm_num)

theorem case11 (hK : SylowTest X B) (h : A312C11 B ⊤) : False :=
  hK 5 1 (by norm_num) (by norm_num) le_rfl (by rw [card_alt6 h.1]; norm_num)
    (by rw [card_top_of (card_m11 h.2)]; norm_num)

theorem case12 (hK : SylowTest X B) (h : A312C12 B ⊤) : False := by
  rcases h with ⟨hB | hB, hL⟩ | ⟨hB | hB, hL⟩
  · exact test_ext hK hB (r := 5) (k := 1) (by norm_num) (by norm_num) le_rfl
      (fun Q _ hQ => by rw [card_alt5 hQ]; norm_num) (by rw [card_top_of (card_m22 hL)]; norm_num)
  · exact test_ext hK hB (r := 5) (k := 1) (by norm_num) (by norm_num) le_rfl
      (fun Q _ hQ => by rw [card_alt6 hQ]; norm_num) (by rw [card_top_of (card_m22 hL)]; norm_num)
  · exact test_ext hK hB (r := 5) (k := 1) (by norm_num) (by norm_num) le_rfl
      (fun Q _ hQ => by rw [card_alt5 hQ]; norm_num)
      (by rw [card_top_of (card_hatm22 hL)]; norm_num)
  · exact test_ext hK hB (r := 5) (k := 1) (by norm_num) (by norm_num) le_rfl
      (fun Q _ hQ => by rw [card_hat6 hQ]; norm_num)
      (by rw [card_top_of (card_hatm22 hL)]; norm_num)

theorem case14 (hK : SylowTest X B) (h : A312C14 B ⊤) : False := by
  obtain ⟨hB | hB | hB | hB, hL⟩ := h
  · exact test_ext hK hB (r := 7) (k := 1) (by norm_num) (by norm_num) le_rfl
      (fun Q _ hQ => by rw [card_l42 hQ]; norm_num) (by rw [card_top_of (card_m24 hL)]; norm_num)
  · exact test_ext hK hB (r := 7) (k := 1) (by norm_num) (by norm_num) le_rfl
      (fun Q _ hQ => by rw [card_l32 hQ]; norm_num) (by rw [card_top_of (card_m24 hL)]; norm_num)
  · exact test_ext hK hB (r := 7) (k := 1) (by norm_num) (by norm_num) le_rfl
      (fun Q _ hQ => by rw [card_l32 hQ]; norm_num) (by rw [card_top_of (card_m24 hL)]; norm_num)
  · exact test_ext hK hB (r := 5) (k := 1) (by norm_num) (by norm_num) le_rfl
      (fun Q _ hQ => by rw [card_hat6 hQ]; norm_num) (by rw [card_top_of (card_m24 hL)]; norm_num)

theorem case15 (hK : SylowTest X B) (h : A312C15 B ⊤) : False :=
  hK 5 1 (by norm_num) (by norm_num) le_rfl (by rw [card_alt5 h.1]; norm_num)
    (by rw [card_top_of (card_j1 h.2)]; norm_num)

end CFSG.Quasithin.Vol2.Ch10.A312C
