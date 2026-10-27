module

public import CFSG.RankThree.PartTwo.Sec15.Item1517StepsProofCon
public import CFSG.RankThree.PartTwo.Sec17.RouteWire14
import CFSG.RankThree.PartTwo.Sec17.Item17Q0Proof

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14

theorem step1517Q0_of (h1444 : Item1444S14) (h146 : Item146S14) (hbot : Item145BotS14)
    (h142 : Concl142S14) : Step1517Q0 := by
  intro G _ _ A c L h Y hctx
  have h14 : Sec14Std G A c L := h.toSec14Std
  obtain ⟨-, -, -, -, -, -, hYL, -, -⟩ := hctx.concl1515
  have hY4 : Y ∈ scriptY4 A (lB A) := hctx.mem_y0Star.prop.1
  have hcov : Y = (Y ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y := by
    rw [inf_comm]
    exact hYL
  exact Sec17.Proof17Q0.pCoreOf_mem_scriptQ_of_cover h14 (h1444 G A c L h14) (h146 G A c L h14)
    (hbot G A c L h14) (h142 G A c L h14) hY4 (Or.inl hcov)

end CFSG.RankThree.PartTwo.Sec15
