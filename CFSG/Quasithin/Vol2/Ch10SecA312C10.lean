module

public import CFSG.Quasithin.Vol2.Ch10SecA312C8

public section

namespace CFSG.Quasithin.Vol2.Ch10.A312C

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {X : Type} [Group X] {B : Subgroup X}

theorem case13
    (hK : SylowTest X B) (h : A312C13 B ⊤) : False := by
  obtain ⟨hB | hB | hB | hB | hB | hB | hB, hL⟩ := h
  · exact hK 11 1 (by norm_num) (by norm_num) le_rfl (by rw [card_m22 hB]; norm_num)
      (by rw [card_top_of (card_m23 hL)]; norm_num)
  · exact hK 7 1 (by norm_num) (by norm_num) le_rfl (by rw [card_l34 hB]; norm_num)
      (by rw [card_top_of (card_m23 hL)]; norm_num)
  · exact test_ext hK hB (r := 7) (k := 1) (by norm_num) (by norm_num) le_rfl
      (fun Q _ hQ => by rw [card_alt7 hQ]; norm_num) (by rw [card_top_of (card_m23 hL)]; norm_num)
  · exact test_ext hK hB (r := 7) (k := 1) (by norm_num) (by norm_num) le_rfl
      (fun Q _ hQ => by rw [card_l32 hQ]; norm_num) (by rw [card_top_of (card_m23 hL)]; norm_num)
  · exact test_ext hK hB (r := 7) (k := 1) (by norm_num) (by norm_num) le_rfl
      (fun Q _ hQ => by rw [card_l32 hQ]; norm_num) (by rw [card_top_of (card_m23 hL)]; norm_num)
  · exact test_ext hK hB (r := 5) (k := 1) (by norm_num) (by norm_num) le_rfl
      (fun Q _ hQ => by rw [card_alt6 hQ]; norm_num) (by rw [card_top_of (card_m23 hL)]; norm_num)
  · exact test_ext hK hB (r := 5) (k := 1) (by norm_num) (by norm_num) le_rfl
      (fun Q _ hQ => by rw [card_alt5 hQ]; norm_num) (by rw [card_top_of (card_m23 hL)]; norm_num)

theorem case17
    (hK : SylowTest X B) (h : A312C17 B ⊤) : False := by
  obtain ⟨hL, hB | hB | hB | hB | hB | hB⟩ := h
  · exact test_ext hK hB (r := 7) (k := 1) (by norm_num) (by norm_num) le_rfl
      (fun Q _ hQ => by rw [card_hatm22 hQ]; norm_num) (by rw [card_top_of (card_j4 hL)]; norm_num)
  · exact test_ext hK hB (r := 7) (k := 1) (by norm_num) (by norm_num) le_rfl
      (fun Q _ hQ => by rw [card_m24 hQ]; norm_num) (by rw [card_top_of (card_j4 hL)]; norm_num)
  · exact test_modO2 hK (r := 5) (k := 1) (by norm_num) (by norm_num) le_rfl
      (by rw [card_alt5 hB]; norm_num) (by rw [card_top_of (card_j4 hL)]; norm_num)
  · exact test_modO2 hK (r := 5) (k := 1) (by norm_num) (by norm_num) le_rfl
      (by rw [card_hat6 hB]; norm_num) (by rw [card_top_of (card_j4 hL)]; norm_num)
  · exact test_modO2 hK (r := 7) (k := 1) (by norm_num) (by norm_num) le_rfl
      (by rw [card_l42 hB]; norm_num) (by rw [card_top_of (card_j4 hL)]; norm_num)
  · exact test_modO2 hK (r := 7) (k := 1) (by norm_num) (by norm_num) le_rfl
      (by rw [card_l32 hB]; norm_num) (by rw [card_top_of (card_j4 hL)]; norm_num)

theorem case18 (hK : SylowTest X B)
    (hs : ¬ A312PairStructCase B) (h : A312C18 B ⊤) : False := by
  obtain ⟨hB | hB, hL⟩ := h
  · exact hs (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hB, hL⟩))))))
  · exact test_ext hK hB (r := 7) (k := 1) (by norm_num) (by norm_num) le_rfl
      (fun Q _ hQ => by rw [card_l32 hQ]; norm_num) (by rw [card_top_of (card_hs hL)]; norm_num)

theorem case19 (hK : SylowTest X B)
    (hs : ¬ A312PairStructCase B) (h : A312C19 B ⊤) : False := by
  obtain ⟨hB | hB, hL⟩ := h
  · exact hs (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hB, hL⟩)))))))
  · exact test_ext hK hB (r := 3) (k := 3) (by norm_num) (by norm_num) (by norm_num)
      (fun Q _ hQ => by rw [card_hat6 hQ]; norm_num) (by rw [card_top_of (card_he hL)]; norm_num)

theorem case20 (hK : SylowTest X B)
    (hs : ¬ A312PairStructCase B) (h : A312C20 B ⊤) : False := by
  obtain ⟨hB | hB, h11, hL⟩ := h
  · exact hs (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hB, h11, hL⟩)))))))
  · exact test_modO2 hK (r := 7) (k := 1) (by norm_num) (by norm_num) le_rfl
      (by rw [card_l32 hB]; norm_num) (by rw [card_top_of (card_ru hL)]; norm_num)

end CFSG.Quasithin.Vol2.Ch10.A312C
