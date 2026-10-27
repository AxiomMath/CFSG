module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Shapes
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5ThinSum
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5ThinOneA
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeNatSmallCounts
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalTwoFamilyRows
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenThreeSteinberg
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSmallNaturalCases
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSLThreeTripleExclusion
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeI
import CFSG.LocalAnalysis.UniquenessCase.UC22P22xd
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOrdNatural.OrderOfX

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s168e3_concl163F_of_l3_component
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (h82 : F08.R82 D)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hL3 : IsL3 ↥(lBar V₀ V hV L) 1) :
    Concl163F D V₀ V hV L := by
  classical
  let H := lBar V₀ V hV L
  let A := Mbar D.M V₀ V hV
  let U := commSub (⊤ : Subgroup (Vtil V₀ V hV)) H
  let Z := U ⊓ fixV H
  have hcardH : Nat.card H = 168 := card_eq_of_isL3 hL3
  obtain ⟨t, hc⟩ := s168e3_exists_H5Cfg c hcomp hL3
  have hnatural : s16h_H5RowL3 H U Z → Concl163F D V₀ V hV L := by
    intro hrow
    obtain ⟨k, hk, hSL, hsum⟩ := hrow
    interval_cases k
    · exact (s168e3_false_of_sumOfNat_zero c hcomp hsum).elim
    · exact s168e3_concl163F_of_sl_three_sum_one c h82 hcomp ⟨hSL, hsum⟩
    · rcases s16nt_case162_of_sl_three c hSL hsum with hcase1 | hcase2
      · exact Or.inl (Or.inr (Or.inl hcase1))
      · exact Or.inl (Or.inr (Or.inr (Or.inl hcase2)))
    · exact s168e3_concl163F_of_sl_three_sum_three c h82 hcomp ⟨hSL, hsum⟩
  have hA5excl : s16h_H5RowA5 H U Z → False := by
    rintro ⟨k, hk, (⟨hOm, hSum⟩ | ⟨hAlt, hSum⟩)⟩
    · have h60 : Nat.card H = 60 := by
        have h := (KOrdNat.isOmegaMinus_four_one_le_and_card hOm).2
        norm_num at h
        exact h
      omega
    · have h60 : Nat.card H = 60 := s15_Three_card_alt_five hAlt
      omega
  rcases hc.conc.2.2 with h133 | h2 | h3 | h4
  · exact (s16h_H5_not_pgroup hc h133).elim
  · exact (s16h_H5_not_tensor hc h2).elim
  · rcases s16h_H5_thin_sum hc h3.2.1 with hrow | hrow
    · exact hnatural hrow
    · exact (hA5excl hrow).elim
  ·
    obtain ⟨hirr, ht, hcomp4, h135⟩ := h4
    rcases s16h_H5_thin_one_case4 hc h135 with
      hL3row | hA5row | hSL2two | hSL2three | hO4two | hO4three | hSt8
    · exact hnatural hL3row
    · exact (hA5excl hA5row).elim
    ·
      have h60 : Nat.card H = 60 := by
        have h := P22x.card_of_isL2Ev hSL2two.1
        norm_num at h
        exact h
      omega
    ·
      have h504 : Nat.card H = 504 := by
        have h := P22x.card_of_isL2Ev hSL2three.1
        norm_num at h
        exact h
      omega
    ·
      have h4080 : Nat.card H = 4080 := by
        have h := (KOrdNat.isOmegaMinus_four_one_le_and_card hO4two.1).2
        norm_num at h
        exact h
      omega
    ·
      have h262080 : Nat.card H = 262080 := by
        have h := (KOrdNat.isOmegaMinus_four_one_le_and_card hO4three.1).2
        norm_num at h
        exact h
      omega
    ·
      exact Or.inr (Or.inl
        (case163_1_of_l3_two_rank_eight c hcomp hL3 hirr hSt8.2))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
