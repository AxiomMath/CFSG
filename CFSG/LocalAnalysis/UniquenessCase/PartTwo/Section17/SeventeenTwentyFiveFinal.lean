module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentyFiveHall
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentyFiveShape
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.J2CentralizerHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.L2SzAutRankHolds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.J2KFactHolds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem seventeen_twentyfive_of_inputs
    (D : Data G) (V₀ V : Subgroup G)
    (h17_24 : R17_24At D V₀ V) (h17_20 : R17_20At D V₀ V)
    (h17_22 : R17_22At D V₀ V) (h17_23 : R17_23At D V₀ V)
    (hSg : UC6S846.SigmaStd D)
    (h880 : F08.R880 D)
    (h869 : F08.R869 D) (h127 : R127 D) (hC117 : C117 D V₀ V)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h1114 : R1114 D) (h162 : W3Thm162Ext G)
    (hTor : W3Lem148Torus G) (h1482 : W3Lem148_2 G) (h126 : R126 D) (h111 : W3Thm111 G) :
    R17_25At D V₀ V := by
  have hJ2aut : K_J2_aut_five_rank := k_J2_aut_five_rank_holds
  have hK2 : K_J2_centralizer_shape := k_J2_centralizer_shape_holds
  exact seventeen_twentyfive_of_steps D V₀ V h17_24 h17_20 h17_22 h17_23 hSg h869 h127 hC117
    hx h61
    h1114 h162 hTor h1482 h126 h111
    (fun L c => gap17_25_H2_hall_of c h17_20 h17_22 h17_23 hSg h880 hJ2aut)
    (fun L c _ _ hJ2 _ => gap17_25_H1_shape_of D V₀ V h17_20 hC117 hK2 L c hJ2)
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.k_L2SzAutRank_holds
    k_J2_center_five_holds

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
