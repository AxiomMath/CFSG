module

public import CFSG.Quasithin.EmptyFaithful.S1422AutM12
public import CFSG.Quasithin.EmptyFaithful.S1422Sz
public import CFSG.Quasithin.EmptyFaithful.S142Statements

public section

namespace CFSG.Quasithin

open CFSG.Open

theorem false_of_isL2Quot_one_of_card {G : Type*} [Group G] {H : Subgroup G}
    (hSz : Nat.card ↥(Sz 0) = 20)
    (h : Nonempty (oTwoQuot ↥H ≃* DihedralGroup 5) ∨ Nonempty (oTwoQuot ↥H ≃* ↥(Sz 0)))
    (h1 : IsL2Quot 1 (oTwoQuot ↥H)) : False := by
  have h6 : Nat.card (oTwoQuot ↥H) = 6 := by
    rw [h1.card le_rfl]; norm_num
  rcases h with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · have := Nat.card_congr e.toEquiv
    rw [h6, Nat.card_eq_fintype_card (α := DihedralGroup 5), DihedralGroup.card] at this
    omega
  · have := Nat.card_congr e.toEquiv
    rw [h6, hSz] at this
    omega

theorem false_of_perm_three_of_card {G : Type*} [Group G] {H : Subgroup G}
    (hSz : Nat.card ↥(Sz 0) = 20) (h : Nonempty (oTwoQuot ↥H ≃* Equiv.Perm (Fin 3)))
    (h' : Nonempty (oTwoQuot ↥H ≃* DihedralGroup 5) ∨ Nonempty (oTwoQuot ↥H ≃* ↥(Sz 0))) :
    False := by
  obtain ⟨e⟩ := h
  have h6 : Nat.card (oTwoQuot ↥H) = 6 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]; rfl
  rcases h' with ⟨⟨e'⟩⟩ | ⟨⟨e'⟩⟩
  · have := Nat.card_congr e'.toEquiv
    rw [h6, Nat.card_eq_fintype_card (α := DihedralGroup 5), DihedralGroup.card] at this
    omega
  · have := Nat.card_congr e'.toEquiv
    rw [h6, hSz] at this
    omega

theorem stageTheorem14220_of_inputs (hF112 : F112LegacyPrintedError)
    (hData : Stage1422Data) (hV : Stage1426VleQ) (hLoc : Lemma14221Local)
    (hF431 : F431Statement) (hNS : ModelNotSimple) (hABG : ABGWreathedRecognition)
    (hG22p : G22pAmalgamFacts) (hI46 : CFSG.GH74.M12.S_Asc03_simple)
    (hM12 : M12AmalgamFacts) (hAut : AutM12AmalgamFacts) : StageTheorem14220 := by
  intro G _ _ T M h H hH
  have hSz := card_Sz_zero
  obtain ⟨Y, hY⟩ := hData G T M h
  have hVH : VZ T M ≤ pCoreOf 2 H := hV G T M h H hH
  constructor
  ·
    intro hsmall
    have S : Setting1422 T M Y H := ⟨h, hH, hY, hsmall.elim Or.inl fun h' => Or.inr (Or.inl h')⟩
    rcases S.six_cases hSz hF112 with hC | hC | hC | hC | hC | hC
    · exact Setting1422.tits_case hF431 S (hLoc.tits G T M Y H S hC) hC
    · exact (Setting1422.twoF4_case hF431 hNS S (hLoc.twoF4 G T M Y H S hC) hC).elim
    · exact (Setting1422.g2_case hF431 hNS S (hLoc.g2 G T M Y H S hC) hC).elim
    · exact (false_of_isL2Quot_one_of_card hSz hsmall hC.2.1).elim
    · exact (false_of_isL2Quot_one_of_card hSz hsmall hC.2.1).elim
    · exact (S.autm12_case hSz hAut (hLoc.autM12 G T M Y H S hC) hC).elim
  ·
    intro hsmall
    have S : Setting1422 T M Y H := ⟨h, hH, hY, Or.inr (Or.inr hsmall)⟩
    rcases S.six_cases hSz hF112 with hC | hC | hC | hC | hC | hC
    · exact (false_of_perm_three_of_card hSz hsmall hC.2.1).elim
    · exact (false_of_perm_three_of_card hSz hsmall (Or.inr hC.2.1)).elim
    · exact (Setting1422.g2_case hF431 hNS S (hLoc.g2 G T M Y H S hC) hC).elim
    · exact Or.inr (Setting1422.g22p_case hSz hABG hG22p hVH S (hLoc.g22p G T M Y H S hC) hC)
    · exact Or.inl (Setting1422.m12_case hI46 hM12 hVH S (hLoc.m12 G T M Y H S hC) hC)
    · exact (S.autm12_case hSz hAut (hLoc.autM12 G T M Y H S hC) hC).elim

end CFSG.Quasithin
