module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.CarrierFactsProof
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.KernelTrivialThreeCo1
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.MonsterAmalgamCarrier
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving.KernelCells
public import CFSG.RankThree.PartOne.MultRes.Trim
public import CFSG.Open.MonsterY443Finiteness

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator

open CFSG.Blueprint CFSG.RankThree.PerfectCover CFSG.AGLEmbedding
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster

theorem bigPrimeFacts_carrier_M : BigPrimeFacts .M := by
  have hB {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :=
    Karpilovsky.Proving.kernelTrivialAt_carrier_of_five_le
      CFSG.RankThree.PartOne.MultRes.sporadicResidualKernelsTrim_holds .B (by decide) hp hp5
  have hCo1 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :=
    Karpilovsky.Proving.kernelTrivialAt_carrier_of_five_le
      CFSG.RankThree.PartOne.MultRes.sporadicResidualKernelsTrim_holds .Co1 (by decide) hp hp5
  exact bigPrimeFacts_M CFSG.Open.Open.monster_y443_derived_card
    (kernelTrivialAt_carrier_M_five_of_baby_co1 (hB (by norm_num) le_rfl)
      (hCo1 (by norm_num) le_rfl))
    (kernelTrivialAt_carrier_M_seven_of_baby_co1 (hB (by norm_num) (by norm_num))
      (hCo1 (by norm_num) (by norm_num)))
    kernelTrivialAt_carrier_M_eleven_of_amalgam kernelTrivialAt_carrier_M_thirteen_of_amalgam

theorem nativeRow_M_of_b_three (hB : KernelTrivialAt (NativeSporadic.Carrier .B) 3) :
    Nat.card (hopfMultiplier (NativeSporadic.Carrier .M)) = sporadicMultiplierOrder .M := by
  have hCM := carrierFacts_M CFSG.Open.Open.monster_y443_derived_card
    CFSG.Milestones.fam_m_simplicity
  have : IsSimpleGroup (NativeSporadic.Carrier .M) := hCM.2.1
  exact nativeRow_of_two_zero_three_zero rfl hCM CFSG.EvenSporadicStandard.rowBound_M
    (kernelTrivialAt_carrier_M_three_of_baby_co1 hB kernelTrivialAt_three_Co1)
    bigPrimeFacts_carrier_M

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
