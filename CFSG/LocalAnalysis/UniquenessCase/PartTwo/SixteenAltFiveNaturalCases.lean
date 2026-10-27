module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Fix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3AltBridge
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKCtx
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSmallNaturalCases
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalTwoFamilyRows

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s168e3_concl163F_of_alt_five_sum_one
    {D : UC22.Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (h82 : F08.R82 D)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hrow : s16h_H5A5Sum (lBar V₀ V hV L)
      (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 1) :
    Concl163F D V₀ V hV L := by
  obtain ⟨hAlt, hsum⟩ := s16h_a5Sum_alt hrow
  have hNsum : SumOfNat (fun H U Z => AlternatingNatural H U Z 5)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 1 :=
    s168e3_sumOfNat_alternating_star c hsum
  have hNstar : AlternatingNatural (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 5 :=
    s16k_sumOfNat_one bot_le hNsum
  have hperf : s15KNatPerf ↥(lBar V₀ V hV L)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) :=
    Or.inr (Or.inr (Or.inr (Or.inr ⟨5, by norm_num, hAlt, hNstar⟩)))
  have hL2 : s15ListTwo ↥(lBar V₀ V hV L) := Or.inr hAlt
  exact Or.inl (Or.inl (Or.inr (Or.inl
    (s168e3_case153_2_of_small_natural c h82 hcomp hperf hL2))))

theorem s168e3_concl163F_of_alt_five_sum_two
    {D : UC22.Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hrow : s16h_H5A5Sum (lBar V₀ V hV L)
      (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 2) :
    Concl163F D V₀ V hV L := by
  obtain ⟨hAlt, hsum⟩ := s16h_a5Sum_alt hrow
  rcases s16nt_case162_of_alt_five_eight c (n := 5) le_rfl (by norm_num) hAlt hsum with
    h1 | h2
  · exact Or.inl (Or.inr (Or.inl h1))
  · exact Or.inl (Or.inr (Or.inr (Or.inl h2)))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
