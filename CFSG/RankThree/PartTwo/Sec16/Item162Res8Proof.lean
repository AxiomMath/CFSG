module

public import CFSG.RankThree.PartTwo.Sec15.Item15Res6ProofThetaRoute
import CFSG.RankThree.PartTwo.Sec16.Item162Res7Final

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec17

theorem step162A7OtherFreeMeet_of_items (h153 : Item153MainR) (hn : Claim153NormalR)
    (h1444 : Item1444S14) (h146 : Item146S14) (hbot : Item145BotS14) (h142 : Concl142S14) :
    Step162A7OtherFreeMeet := by
  intro G _ _ A c L hR Y₁ Y₂ S hmax hLY hmeets₁ _ _ _ ha7₁ hnc _ b Lb hb hLb hbc hmeets₂ ha7₂
    hsc hfree _ hcen _
  exact Res162Seven.not_conf683
    { sec15R := hR
      maxCE := hmax
      le_y₁ := hLY
      meets₁ := hmeets₁
      a7₁ := ha7₁
      ne := fun hY => hnc ⟨1, Subgroup.one_mem _, by rw [hY]; ext x; simp⟩
      omega_b := hb
      lA_b := hLb
      ne_c := hbc
      meets₂ := hmeets₂
      a7₂ := ha7₂
      sc₂ := hsc
      free := hfree
      centralizer_le := hcen
      item153 := h153 G A c L hR
      claim153Normal := hn G A c L hR
      item1444 := h1444 G A c L hR.toSec14Std
      item146 := h146 G A c L hR.toSec14Std
      bot := hbot G A c L hR.toSec14Std
      concl142 := h142 G A c L hR.toSec14Std }

theorem item162R_of_res8_core
    (h1514 : Item1514R) (h1523 : Item1523R) (h153 : Item153MainR) (hobs : Claim153ObsR)
    (hn : Claim153NormalR) (h1411 : Item1411_1R) (h155 : Item155R)
    (hWloc : Claim1411NonsolvWR) (hXloc : Claim1411NonsolvXR) (h1444 : Item1444S14)
    (h146 : Item146S14) (hbot : Item145BotS14) (h142 : Concl142S14) (hU35 : Step163U35)
    (hRead : Y4CoreReadR) (hMem : Y4CoreMemR) (h148 : Item148SmallS14) (hCore : Step148Core)
    (hPoint : Step148Point) (hKT : Step148KType) (h135 : Item135) (hOne : Step162UJOddOne) :
    Item162R :=
  item162R_of_res7_core h1514 h1523 h153 hobs hn h1411 h155 hWloc hXloc h1444 h146 hbot h142 hU35
    hRead hMem h148 hCore hPoint hKT h135 hOne
    (step162A7OtherFreeMeet_of_items h153 hn h1444 h146 hbot h142)

end CFSG.RankThree.PartTwo.Sec16
