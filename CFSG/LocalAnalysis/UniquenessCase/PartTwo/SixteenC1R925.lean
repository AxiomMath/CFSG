module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1R925Desc
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1R925PartB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1R925KGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem r925Used_holds
    {G : Type} [Group G] [Finite G]
    (D : Data G) (h82 : F08.R82 D) (hK32 : UCK.K32) (hKSch : UCK.KSch)
    (hGA : CFSG.Open.GriessAllModelsStatement) (hL3U3 : OddIdxPropL3U3) : R925Used D := by
  intro L P X H Y z hL hU hP hX hXne hHM hF hY hXY hO2 hodd hsig hm3 hz hz2 hHz hr3 hrq hsyl hE
  have hctx := r925_descent D h82
    ⟨hL, hU, hP, hX, hXne, hHM, hF, hY, hXY, hO2, hodd, hsig, hm3, hz, hz2, hHz, hr3, hrq, hsyl, hE⟩
  exact r925_partB (oddIdxAll_of_k32 hK32 hL3U3) hK32 hKSch hGA hctx

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
