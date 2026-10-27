module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Cfg
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenLThreeComponentCases
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenAltFiveComponentCases
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSLTwoFourRow
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSLTwoEightRow
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenOmegaFourMinusFourRow
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenOmegaFourMinusEightStd
public import Certificates.Certificate431004
public import Certificates.Certificate17430
public import Certificates.Certificate9726
import CFSG.GroupTheory.CommutatorCentralizerIn
import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreEven
import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreL34
import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreRes
import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeB2s
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsNineB1
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsNineB23
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsThirtyEightOq
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsNineB23
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.UEqZ
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1Rk
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3SL24CoverC
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Rows
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214e2
import CFSG.Quasithin.EmptyFaithful.S14113bMain
import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCShort
import CFSG.RankThree.PartTwo.Sec3.TwoGroupPrimeFiveAction
import CFSG.RankThree.PartTwo.Sec4.Item420
import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210SetupGlobal
import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210SetupOrbit

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s168e3_concl163F_of_thin_component
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (h82 : F08.R82 D)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q (lBar V₀ V hV L) ≤ 1) :
    Concl163F D V₀ V hV L := by
  obtain ⟨t, ht, ht2, ht1, htr, hconc⟩ := c.conc
  have hc : s16h_H5Cfg (Mbar D.M V₀ V hV) (lBar V₀ V hV L) t :=
    ⟨s15_Infra_vtil_sq_eq_one V₀ V hV, ht, ht2, ht1, htr, hconc, hcomp, hthin⟩
  have hL3 : s16h_H5RowL3 (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) → Concl163F D V₀ V hV L := by
    rintro ⟨-, -, hSL, -⟩
    exact s168e3_concl163F_of_l3_component c h82 hcomp
      (s16k_isLn_of_isSLn (by norm_num : 3 ≤ 3) hSL)
  have hA5 : s16h_H5RowA5 (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) → Concl163F D V₀ V hV L := by
    rintro ⟨-, -, ⟨hO, -⟩ | ⟨hA, -⟩⟩
    · exact s168e3_concl163F_of_alt_five_component c h82 hcomp
        (s16k_isAlt_five_of_isOmegaMinus_four hO)
    · exact s168e3_concl163F_of_alt_five_component c h82 hcomp hA
  rcases hc.conc.2.2 with h133 | h2 | h3 | h4
  · exact (s16h_H5_not_pgroup hc h133).elim
  · exact (s16h_H5_not_tensor hc h2).elim
  · rcases s16h_H5_thin_sum hc h3.2.1 with hrow | hrow
    · exact hL3 hrow
    · exact hA5 hrow
  · obtain ⟨-, -, -, h135⟩ := h4
    rcases s16h_H5_thin_one_case4 hc h135 with
      hrow | hrow | hrow | hrow | hrow | hrow | hrow
    · exact hL3 hrow
    · exact hA5 hrow
    · exact s168e3_concl163F_of_sl2_four c hcomp hthin hrow
    · exact s168e3_concl163F_of_sl2_eight c hcomp hthin hrow
    · exact s168e3_concl163F_of_omegaMinus_four_four c hcomp hthin hrow
    · exact s168e3_concl163F_of_omegaMinus_four_eight_of_std c h82 hcomp hthin hrow
    · exact s168e3_concl163F_of_l3_component c h82 hcomp hrow.1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
