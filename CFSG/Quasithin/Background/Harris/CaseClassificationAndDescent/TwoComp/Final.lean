module

public import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp.Excl
public import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp.Omega4Plus
public import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp.L3Tensor
public import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp.Surv15
public import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp.Surv14
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Quasithin.G11.Harris
  CFSG.Assembly.LowTwoRank

theorem isPSL_two_two_two_of_isPSL_two_five {X : Type} [Group X]
    (h : IsPSL 2 5 1 X) : IsPSL 2 2 2 X := by
  obtain ⟨-, K, hKf, hKfin, hK, ⟨eX⟩⟩ := h
  obtain ⟨e5⟩ :=
    CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five K
      (Or.inr (hK.trans (by norm_num)))
  have hK2 : Nat.card (GaloisField 2 2) = 2 ^ 2 := GaloisField.card 2 2 (by norm_num)
  have hK4 : Nat.card (GaloisField 2 2) = 4 := hK2.trans (by norm_num)
  obtain ⟨e'⟩ :=
    CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five (GaloisField 2 2)
      (Or.inl hK4)
  refine ⟨⟨Nat.prime_two, by norm_num, by norm_num, by norm_num, by norm_num⟩, ?_⟩
  exact ⟨GaloisField 2 2, inferInstance, inferInstance, hK2, ⟨(eX.trans e5).trans e'.symm⟩⟩


theorem eq_one_of_pow_le {p e : ℕ} (hp3 : 3 < p) (he1 : 1 ≤ e) (h : p ^ e ≤ 7) : e = 1 := by
  by_contra hne
  have h1 : p ^ 2 ≤ p ^ e := Nat.pow_le_pow_right (by omega) (by omega)
  nlinarith

theorem twoComp_holds
    : CFSG.Quasithin.G11.Harris.TwoComp := by
  intro V _ _ _ Γ A L H m h hex
  obtain ⟨L₂, hc, hne, hH, hq⟩ := hex
  have hs : Setting Γ A L L₂ m := Setting.of_data h hc hne hH hq
  subst hH
  rcases hs.types with ⟨n, hn⟩ | ⟨n, hn⟩ | hJ1 | ⟨p, e, hp, hp3, he1, he2, hpe⟩
  ·
    have hn2 : 2 ≤ n := by
      obtain ⟨⟨-, hf1, -, hne2, -⟩, -⟩ := hn
      by_contra hlt
      have : n = 1 := by omega
      subst this
      exact hne2 (by simp)
    obtain ⟨hd, hm1, hm2, hT⟩ := hs.tensor15 hn2 hn
    obtain ⟨hnat, hend, hsd⟩ := isNaturalMatrixModule_of_isTensorModel_two hn2 hT
    exact Or.inr ⟨n, ⟨hn2, hd, hm1, hm2, hnat⟩, hend, hsd⟩
  ·
    obtain ⟨-, a, ha, K, -, -, hfa, -, -⟩ := id hn
    exact (hs.false_of_suzuki (by rw [hfa]; exact odd_two_mul_add_one a) (by omega) hn).elim
  · exact (hs.false_of_j1 hJ1).elim
  · by_cases h5 : p ^ e = 5
    ·
      have he1' : e = 1 := eq_one_of_pow_le hp3 he1 (by omega)
      subst he1'
      have hp5 : IsPSL 2 5 1 (↥L ⧸ Subgroup.center ↥L) := by
        have : p = 5 := by simpa using h5
        subst this
        exact hpe
      have hn := isPSL_two_two_two_of_isPSL_two_five hp5
      obtain ⟨hd, hm1, hm2, hT⟩ := hs.tensor15 (n := 2) le_rfl hn
      obtain ⟨hnat, hend, hsd⟩ := isNaturalMatrixModule_of_isTensorModel_two (n := 2) le_rfl hT
      exact Or.inr ⟨2, ⟨le_rfl, hd, hm1, hm2, hnat⟩, hend, hsd⟩
    · by_cases h7 : p ^ e = 7
      · have he1' : e = 1 := eq_one_of_pow_le hp3 he1 (by omega)
        subst he1'
        have hp7 : IsPSL 2 7 1 (↥L ⧸ Subgroup.center ↥L) := by
          have : p = 7 := by simpa using h7
          subst this
          exact hpe
        obtain ⟨hd, hm, hT⟩ := hs.tensor14 hp7
        obtain ⟨hend, hnsd⟩ := endIsField_and_not_selfDual_of_isTensorModel_three hT
        exact Or.inl ⟨⟨hm, hd, hT⟩, hend, hnsd⟩
      · exact (hs.false_of_oddL2 hp hp3 he1 he2 ⟨h5, h7⟩ hpe).elim

end CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp
