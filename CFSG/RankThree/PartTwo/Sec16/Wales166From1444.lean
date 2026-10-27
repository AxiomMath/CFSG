module

public import CFSG.RankThree.PartTwo.Sec16.Item166OmegaSzFive
import CFSG.RankThree.PartTwo.Sec16.Item166Res4Proof
import CFSG.RankThree.PartTwo.Sec16.SuzukiSectionProofGL
import CFSG.RankThree.PartTwo.Sec15.Item15Res8ProofStar
public import CFSG.RankThree.PartTwo.Sec15.Y4CoreProofDefs
public import CFSG.RankThree.PartTwo.Sec16.Item166ResProofDeltaSz
public import CFSG.RankThree.PartTwo.Sec16.Item166ResProofRoute
public import CFSG.RankThree.PartTwo.Sec17.Item17HeadProof

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec17
  CFSG.RankThree.PartTwo.Late CFSG.RankThree.LocalRank CFSG.GH74.GLS

theorem step166Gen_of_1444 (h146 : Item146S14)
    (h1444 : Item1444S14) (hbot : Item145BotS17) (h142 : Concl142R) : Step166Gen :=
  step166Gen_of' h146 (step166DeltaSz_of_item1444 h146 h1444 hbot h142)

theorem step166GenHJ_of_1444 (h146 : Item146S14)
    (h1444 : Item1444S14) (hbot : Item145BotS17) (h142 : Concl142R) : Step166GenHJ :=
  step166GenHJ_of' h146 (step166DeltaSzHJ_of (step166DeltaSz_of_item1444 h146 h1444 hbot h142))

theorem item166S17_of_1444
    (h2 : Step166ThetaTwo) (h146 : Item146S14) (h1444 : Item1444S14) (hbot : Item145BotS17)
    (h142 : Concl142R) (h1514 : Item1514S17) (hMeets : Claim1715Meets) (hL3 : KSL3PiNoSz)
    (h165 : Item165S17) (hΩ : Step166OmegaNot2n) (hctr : Step166CtrNot2n) : Item166S17 :=
  item166S17_of_steps_not2n h2 h146 (step166DeltaSz_of_item1444 h146 h1444 hbot h142) h1514
    hMeets hL3 h165 hΩ hctr

section OmegaMeets

theorem step166OmegaA5HJ_of_meets_1444 (h146 : Item146S14) (h1444 : Item1444S14)
    (hbot : Item145BotS17) (h142 : Concl142R) (h1514 : Item1514S17)
    (hMeets : Claim1715Meets) : Step166OmegaA5HJ := by
  intro G _ _ A c L Y₀ h hJ
  have hY : Y₀ = L ⊔ CFSG.Open.pCoreOf 2 Y₀ :=
    (rank3II_17_15_HJ_of h (h1514 G A c L Y₀ h) (hMeets G A c L Y₀ h) hJ).2.1
  obtain ⟨hrk, hZ⟩ := Proof166SzFive.five_rank_center_of_j2 h hJ hY
  exact Proof166SzFive.omega166A5_of_five_rank h
    (step166GenHJ_of_1444 h146 h1444 hbot h142 G A c L Y₀ h hJ)
    (step166NoSz_of_items h1514 hMeets G A c L Y₀ h) hrk hZ

theorem step166OmegaThreeHJ_of_meets_1444 (h146 : Item146S14) (h1444 : Item1444S14)
    (hbot : Item145BotS17) (h142 : Concl142R) (h1514 : Item1514S17)
    (hMeets : Claim1715Meets) : Step166OmegaThreeHJ := by
  intro G _ _ A c L Y₀ h hJ
  have hY : Y₀ = L ⊔ CFSG.Open.pCoreOf 2 Y₀ :=
    (rank3II_17_15_HJ_of h (h1514 G A c L Y₀ h) (hMeets G A c L Y₀ h) hJ).2.1
  obtain ⟨hrk, hZ⟩ := Proof166SzFive.five_rank_center_of_j2 h hJ hY
  exact Proof166SzFive.omega166Three_of_five_rank h
    (step166GenHJ_of_1444 h146 h1444 hbot h142 G A c L Y₀ h hJ)
    (step166NoSz_of_items h1514 hMeets G A c L Y₀ h) hrk hZ

end OmegaMeets

section OmegaOf

theorem step166OmegaA5HJ_of_1444 (h146 : Item146S14) (h1444 : Item1444S14)
    (hbot : Item145BotS17) (h142 : Concl142R) (h1523 : Sec15.Item1523R) :
    Step166OmegaA5HJ := by
  intro G _ _ A c L Y₀ h hJ
  have hY : Y₀ = L ⊔ CFSG.Open.pCoreOf 2 Y₀ := by
    have h1 := (h1523 G A c L h.toSec15R hJ Y₀ h.mem_y0Star).1
    rwa [inf_of_le_right h.le_y0] at h1
  obtain ⟨hrk, hZ⟩ := Proof166SzFive.five_rank_center_of_j2 h hJ hY
  exact Proof166SzFive.omega166A5_of_five_rank h
    (step166GenHJ_of_1444 h146 h1444 hbot h142 G A c L Y₀ h hJ)
    (noSz166_hj_of h1523 G A c L Y₀ h hJ) hrk hZ

theorem step166OmegaThreeHJ_of_1444 (h146 : Item146S14) (h1444 : Item1444S14)
    (hbot : Item145BotS17) (h142 : Concl142R) (h1523 : Sec15.Item1523R) :
    Step166OmegaThreeHJ := by
  intro G _ _ A c L Y₀ h hJ
  have hY : Y₀ = L ⊔ CFSG.Open.pCoreOf 2 Y₀ := by
    have h1 := (h1523 G A c L h.toSec15R hJ Y₀ h.mem_y0Star).1
    rwa [inf_of_le_right h.le_y0] at h1
  obtain ⟨hrk, hZ⟩ := Proof166SzFive.five_rank_center_of_j2 h hJ hY
  exact Proof166SzFive.omega166Three_of_five_rank h
    (step166GenHJ_of_1444 h146 h1444 hbot h142 G A c L Y₀ h hJ)
    (noSz166_hj_of h1523 G A c L Y₀ h hJ) hrk hZ

end OmegaOf

section Wiring

theorem item166S17_of_1444_five (h146 : Item146S14) (h1444 : Item1444S14)
    (hbot : Item145BotS17) (h142 : Concl142R) (h1514 : Item1514S17)
    (hMeets : Claim1715Meets) (h165 : Item165S17) (hRead : Y4CoreReadR)
    (hMem : Y4CoreMemR) (h152 : Item152R) (h155 : Item155R) (h148 : Item148R)
    (hA5Ctr : Step166CtrA5HJ) (hthree : Step166OmegaThreeOther) : Item166S17 :=
  item166S17_of_1444 step166ThetaTwo h146 h1444 hbot h142 h1514 hMeets kSL3PiNoSz_holds h165
    (step166OmegaNot2n_of_core hRead hMem h152 h155 h148 hbot h1514 hMeets
      (step166OmegaA5HJ_of_meets_1444 h146 h1444 hbot h142 h1514 hMeets) hthree
      (step166OmegaThreeHJ_of_meets_1444 h146 h1444 hbot h142 h1514 hMeets))
    (step166CtrNot2n_of_core hRead hMem h152 h155 h148 hbot h1514 hMeets hA5Ctr)

end Wiring

end CFSG.RankThree.PartTwo.Sec16
