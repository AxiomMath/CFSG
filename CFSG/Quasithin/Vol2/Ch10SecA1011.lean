module

public import CFSG.Quasithin.Vol2.Ch10SecA1012Four

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem not_cases13_of_suzuki {n : ℕ}
    (hsz : CFSG.Blueprint.SuzukiModel (↥L ⧸ CFSG.pCore 2 ↥L) 2 n) :
    ¬ ((∃ m, Ch10.Case10_1_1One T L I m) ∨ Ch10.Case10_1_1Three T L I) := by
  obtain ⟨-, a, -, K, _, _, hf, hK, ⟨e⟩⟩ := hsz
  subst hf
  have hc := (Nat.card_congr e.toEquiv).trans (CFSG.LieType.Ree.suzuki_order hK)
  rintro (⟨m, -, ⟨K', _, _, hK', ⟨e'⟩⟩, -⟩ | ⟨⟨e'⟩, -⟩)
  · rw [Nat.card_congr e'.toEquiv, card_SL_two_pow hK'] at hc
    refine three_not_dvd_card_suzuki a (hc ▸ Dvd.dvd.mul_left ?_ _)
    simpa [pow_mul] using three_dvd_two_pow_two_mul_sub_one m
  · rw [Nat.card_congr e'.toEquiv, card_SL_three_zmod_two] at hc
    exact three_not_dvd_card_suzuki a (hc ▸ (by norm_num : 3 ∣ 168))

theorem case_seven_of_weak
    (hF : Facts10_1) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h322 : TmpL6_3_2_2_two) (hshape : Stmt7_0_1_shape)
    (h42 : AsB42) (h51 : AsB51) (h154 : AsB15Part4) (h116 : ASInputs.AS_I_1_6_one)
    (h3210 : TmpL6_3_2_10_nine) (hyp : Ch10.Hyp10 G T L I) (h : Case10_1_1SevenWeak T L I) :
    Ch10.Case10_1_1Seven T L I := by
  obtain ⟨n, hsz, hab, hmod⟩ := h
  have hC := fsuCVM_eq_bot hF h37 h38 h322 hshape h42 h51 h154 h116 h3210 hyp
    (not_cases13_of_suzuki hsz)
  have hLV : L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (le_fsuL0 T L).trans (fsuL0_le_normalizer_fsuVM T L I)
  have hUV : fsuUL T L I ≤ fsuVM T L I := Subgroup.le_normalizer_iff_commutator_le_left.mp hLV
  have hcV1 : Ch10.cV1 T L I = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    rw [Ch10.cV1, Subgroup.mem_subgroupOf] at hu
    have h1 : (u : G) ∈ fsuCVM T L I := ⟨hUV u.2, hu⟩
    rw [hC, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.mpr (Subtype.ext h1)
  rw [hcV1] at hmod
  exact ⟨n, hsz, hab, hmod⟩

theorem cases10_1_1
    (hF : Facts10_1) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h322 : TmpL6_3_2_2_two) (hshape : Stmt7_0_1_shape)
    (h42 : AsB42) (h45 : AsB45) (h51 : AsB51) (h154 : AsB15Part4)
    (h116 : ASInputs.AS_I_1_6_one) (h16 : ASInputs.AS_I_1_6) (h3210 : TmpL6_3_2_10_nine)
    (hyp : Ch10.Hyp10 G T L I) : Ch10.Cases10_1_1 T L I := by
  obtain ⟨hab, -, -, -, -, -, hc⟩ := hyp.three
  rcases hc with ⟨hUI, -⟩ | ⟨-, -, hcard, s, hsT, hsN, hsO, hU, hinf⟩ | hiii
  · rcases cases_of_one hF h37 h38 h322 hshape h45 h116 h16 hyp hUI with
      h | h | h | ⟨n, h, -⟩ | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, h⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (case_seven_of_weak hF h37 h38 h322 hshape h42 h51 h154 h116 h3210 hyp h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (case_five_of h37 h38 hshape hyp hcard hsT hsN hsO hU hinf)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (case_six_of h37 h38 hyp hiii))))))

theorem stmt10_1_1_of
    (hF : Facts10_1) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h322 : TmpL6_3_2_2_two) (hshape : Stmt7_0_1_shape)
    (h42 : AsB42) (h45 : AsB45) (h51 : AsB51) (h154 : AsB15Part4)
    (h116 : ASInputs.AS_I_1_6_one) (h16 : ASInputs.AS_I_1_6) (h3210 : TmpL6_3_2_10_nine) :
    Stmt10_1_1 := by
  intro G _ _ T L I hyp
  have h := stmt10_1_1_structure h37 h38 h322 hyp
  exact ⟨h.1, h.2.1, h.2.2,
    cases10_1_1 hF h37 h38 h322 hshape h42 h45 h51 h154 h116 h16 h3210 hyp⟩

end CFSG.Quasithin.Vol2.Ch10.SecA
