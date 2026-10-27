module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenAltFiveTripleCases
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenAltFiveNaturalCases
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSmallComponentBounds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeNatSmallCounts
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Shapes
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5ThinSum
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5ThinOneA
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSLTwoFourRow
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeI
import CFSG.LocalAnalysis.UniquenessCase.UC22P22xd
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOrdNatural.OrderOfX

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s168e3_concl163F_of_alt_five_component
    {D : UC22.Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (h82 : F08.R82 D)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hA5 : UC22.IsAlt ↥(lBar V₀ V hV L) 5) :
    Concl163F D V₀ V hV L := by
  classical
  let H := lBar V₀ V hV L
  let A := Mbar D.M V₀ V hV
  let U := commSub (⊤ : Subgroup (Vtil V₀ V hV)) H
  let Z := U ⊓ fixV H
  have hcardH : Nat.card H = 60 := s15_Three_card_alt_five hA5
  have hthin : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q H ≤ 1 :=
    fun q hq hq2 => pRank_le_one_of_card_eq_sixty hcardH hq hq2
  obtain ⟨t, ht, ht2, ht1, htr, hconc⟩ := c.conc
  have hc : s16h_H5Cfg A H t :=
    ⟨s15_Infra_vtil_sq_eq_one V₀ V hV, ht, ht2, ht1, htr, hconc, hcomp, hthin⟩
  have hnatural : s16h_H5RowA5 H U Z → Concl163F D V₀ V hV L := by
    rintro ⟨k, hk, hrowk⟩
    interval_cases k
    · obtain ⟨-, hsum⟩ := s16h_a5Sum_alt hrowk
      exact (s168e3_false_of_sumOfNat_zero c hcomp hsum).elim
    · exact s168e3_concl163F_of_alt_five_sum_one c h82 hcomp hrowk
    · exact s168e3_concl163F_of_alt_five_sum_two c hrowk
    · exact s168e3_concl163F_of_alt_five_sum_three c h82 hcomp hrowk
  have hL3excl : s16h_H5RowL3 H U Z → False := by
    rintro ⟨k, hk, hSL, -⟩
    have h168 : Nat.card H = 168 :=
      card_eq_of_isL3 (s16k_isLn_of_isSLn (by norm_num : 3 ≤ 3) hSL)
    omega
  rcases hc.conc.2.2 with h133 | h2 | h3 | h4
  · exact (s16h_H5_not_pgroup hc h133).elim
  · exact (s16h_H5_not_tensor hc h2).elim
  · rcases s16h_H5_thin_sum hc h3.2.1 with hrow | hrow
    · exact (hL3excl hrow).elim
    · exact hnatural hrow
  ·
    obtain ⟨-, -, -, h135⟩ := h4
    rcases s16h_H5_thin_one_case4 hc h135 with
      hL3row | hA5row | hSL2two | hSL2three | hO4two | hO4three | hSt8
    · exact (hL3excl hL3row).elim
    · exact hnatural hA5row
    ·
      exact s168e3_concl163F_of_sl2_four c hcomp hthin hSL2two
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
      have h168 : Nat.card H = 168 := card_eq_of_isL3 hSt8.1
      omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
