module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyEightKTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyEightShape
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyEightComponentB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CatalogueThreePrimeHolds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.BorelTorusAbelianHolds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem seventeen_sixtyeight
    {D : Data G} {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    (h1 : R17_1At D V₀ V hV) (h3 : R17_3At D V₀ V) (h22 : R17_2_2At D V₀ V hV)
    (h23 : R17_2_3At D V₀ V hV) (h33 : R17_33_2At D V₀ V) (h42 : R17_42At D V₀ V)
    (h55 : R17_55At D V₀ V) (h57 : R17_57At D V₀ V)
    (h641 : R17_64_1At D V₀ V) (h642 : R17_64_2At D V₀ V) (h643 : R17_64_3At D V₀ V)
    (hThin : ThinList13) (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian)
    (h638 : UC6.R6_38 D) (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D)
    (hDE : DataExt D) (hR82 : F08.R82 D) :
    R17_68At D V₀ V := by
  have hK3 : Inputs1719.K_BorelTorusAbelian := Inputs1719.k_BorelTorusAbelian_holds
  have h56 : R17_56At D V₀ V := seventeen_fiftysix D V₀ V hThin hCyc h638 h33
  intro p hp L hL X hX hX0 hAlt
  by_cases hXL : X = L
  · exact seventeen_sixtyeight_of_eq_self hV h42 h56 h57 h641 h642 h643 hThin hCyc h638
      h33 h22 h23 hDE p hp L hL X hX hX0 hAlt hXL
  ·
    have hne : conjClosure D.M L ≠ L := hX ▸ hXL
    obtain ⟨hp5, L', c⟩ := ctx1768_of_ne h42 hp hL hne hAlt
    by_cases hA : ∀ J ∈ calC D.M, J ∈ conjSetOf D.M L
    ·
      refine ⟨hp5, eM_eq_three_of_evenRank hDE c.h5 c.he3, ?_, ?_⟩
      · exact isA5A5Cyclic5_of_layer_le D hV h22 h23 h638 hDE c.h5 c.he3
          (Ctx1768.conjClosure_le c) (Ctx1768.normal c) c.isA5xA5_barImage
          (layer_le_barImage_conjClosure hA)
      · exact Hinf_oTwoEOf_le_Opp_five_of_layer_le (Ctx1768.conjClosure_le c)
          (Ctx1768.le_normalizer c) (Ctx1768.perfect c) (Ctx1768.isA5xA5_bar2 c)
          (layer_le_barImage_conjClosure hA)
    ·
      push_neg at hA
      obtain ⟨J, hJ, hJL⟩ := hA
      exact (false_of_not_mem_conjSetOf c hSg hR82
        (k_eq_two_of_conj_pair h1 hK3 c.hL c.hL' c.hne c.hL'conj c.hX c.hAlt)
        CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.k_CatalogueThreePrimeSz_holds
        h55 h3 hJ hJL).elim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
