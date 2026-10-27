module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalTwoFamilyRows
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenLargeClassicalComponent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenLargeAlternatingComponent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSLSixSevenTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSmallShapes
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3Def
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumConvFive
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKOmegaPlusSix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumConvEight

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s168e3_concl163F_of_sumOfNatShape_two
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hsum : SumOfNatShape (lBar V₀ V hV L)
      (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 2) :
    Concl163F D V₀ V hV L := by
  rcases hsum with ⟨n, ⟨hSL, hsum⟩ | ⟨hSp, hsum⟩ | ⟨hOp, hsum⟩ | ⟨hOm, hsum⟩ | ⟨hAlt, hsum⟩⟩
  ·
    have hn3 : 3 ≤ n := s16k_three_le_of_isSLn hcomp.2.2 hSL
    by_cases hn8 : 8 ≤ n
    · exact (s168e3_false_of_sl_component_ge_eight c hcomp hn8 hSL).elim
    · by_cases hn67 : n = 6 ∨ n = 7
      · exact (s16nt_sl_six_seven_two_false c hcomp hn67 hSL hsum).elim
      · have hn : n = 3 ∨ n = 4 ∨ n = 5 := by omega
        rcases hn with rfl | rfl | rfl
        · exact s16nt_concl163F_of_natural_two_family c hcomp
            (Or.inr (Or.inr (Or.inl ⟨hSL, hsum⟩)))
        · exact s16nt_concl163F_of_natural_two_family c hcomp
            (Or.inr (Or.inr (Or.inr (Or.inl ⟨hSL, hsum⟩))))
        · exact s16nt_concl163F_of_natural_two_family c hcomp
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hSL, hsum⟩)))))
  ·
    have hn6 : 6 ≤ n := s16k_six_le_of_isSpn hcomp.2.2 hSp
    obtain ⟨k, hk⟩ := hSp.1
    by_cases hn8 : 8 ≤ n
    · exact (s168e3_false_of_sp_component_ge_eight c hcomp hn8 hSp).elim
    · have hn : n = 6 := by omega
      subst hn
      exact s16nt_concl163F_of_natural_two_family c hcomp
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hSp, hsum⟩))))))
  ·
    have hn6 : 6 ≤ n := s16k_six_le_of_isOmegaPlus hcomp.2.2 hOp
    obtain ⟨k, hk⟩ := hOp.1
    by_cases hn8 : 8 ≤ n
    · exact (s168e3_false_of_omegaPlus_component_ge_eight c hcomp hn8 hOp).elim
    · have hn : n = 6 := by omega
      subst hn
      have hA8 : UC22.IsAlt ↥(lBar V₀ V hV L) 8 := s15k_omp6_isAlt8 hOp
      have hsum8 : SumOfNat (fun H U Z => AlternatingNatural H U Z 8)
          (lBar V₀ V hV L) (wTil V₀ V hV L)
          (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 2 := by
        obtain ⟨I, hZI, hind, hsup, hN⟩ := hsum
        exact ⟨I, hZI, hind, hsup, fun i =>
          s16k_alternatingNatural_eight_of_natOmegaPlus_six (hN i)⟩
      exact s16nt_concl163F_of_natural_two_family c hcomp
        (Or.inl ⟨8, by norm_num, by norm_num, hA8, hsum8⟩)
  ·
    have hn4 : 4 ≤ n := s16k_four_le_of_isOmegaMinus hcomp.2.2 hOm
    obtain ⟨k, hk⟩ := hOm.1
    by_cases hn10 : 10 ≤ n
    · exact (s168e3_false_of_omegaMinus_component_ge_ten c hcomp hn10 hOm).elim
    · have hn : n = 4 ∨ n = 6 ∨ n = 8 := by omega
      rcases hn with rfl | rfl | rfl
      ·
        have hA5 : UC22.IsAlt ↥(lBar V₀ V hV L) 5 :=
          s16k_isAlt_five_of_isOmegaMinus_four hOm
        have hsum5 : SumOfNat (fun H U Z => AlternatingNatural H U Z 5)
            (lBar V₀ V hV L) (wTil V₀ V hV L)
            (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 2 := by
          obtain ⟨I, hZI, hind, hsup, hN⟩ := hsum
          exact ⟨I, hZI, hind, hsup, fun i =>
            s16k_alternatingNatural_five_of_natOmegaMinus_four (hN i)⟩
        exact s16nt_concl163F_of_natural_two_family c hcomp
          (Or.inl ⟨5, le_rfl, by norm_num, hA5, hsum5⟩)
      · exact s16nt_concl163F_of_natural_two_family c hcomp
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hOm, hsum⟩)))))))
      · exact s16nt_concl163F_of_natural_two_family c hcomp
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hOm, hsum⟩)))))))
  ·
    have hn5 : 5 ≤ n := s16k_five_le_of_isAlt hcomp.2.2 hAlt
    by_cases hn12 : 12 ≤ n
    · exact (s168e3_false_of_alternating_component_ge_twelve c hcomp hn12 hAlt).elim
    · by_cases hn8 : n ≤ 8
      · exact s16nt_concl163F_of_natural_two_family c hcomp
          (Or.inl ⟨n, hn5, hn8, hAlt, hsum⟩)
      · have hn9 : 9 ≤ n := by omega
        have hn11 : n ≤ 11 := by omega
        exact s16nt_concl163F_of_natural_two_family c hcomp
          (Or.inr (Or.inl ⟨n, hn9, hn11, hAlt, hsum⟩))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
