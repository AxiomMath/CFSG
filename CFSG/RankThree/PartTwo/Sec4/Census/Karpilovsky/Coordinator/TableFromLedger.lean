module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ProvedRows
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.SuzRow
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.M12CoverRow
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.J2CoverRow
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.J3CoverCert
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONCoverCert
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi22DoubleCover
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi22TripleCover
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24ThreeCover
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.KernelTrivialThreeCo2
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.KernelTrivialThreeCo3
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.LyKernelTrivialThree
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.KernelTrivialThreeTh
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.MonsterRow
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.BThreeFromFi23
public import CFSG.LocalAnalysis.EvenSporadicStandard.CentralTwoCo2
public import CFSG.LocalAnalysis.EvenSporadicStandard.CentralTwoFischer
public import CFSG.LocalAnalysis.EvenSporadicStandard.CentralTwoTh
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.DoubleCoversCo1B

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator

open CFSG.Blueprint CFSG.RankThree.PerfectCover CFSG.AGLEmbedding CFSG.EvenSporadicStandard


theorem nativeSporadicMultipliers_of_ledger (hBig : ∀ s, s ≠ .M → BigPrimeFacts s)
    (h : SporadicOpenCells) : NativeSporadicMultipliers := by
  have hC : ∀ s, s ≠ .M → CarrierFacts s := carrierFacts_of_ne_M
  intro s
  cases s with
  | M11 => exact nativeRow_M11
  | M12 => exact nativeRow_M12
  | M22 => exact nativeRow_M22
  | M23 => exact nativeRow_M23
  | M24 => exact nativeRow_M24
  | J1 => exact nativeRow_J1
  | J2 => exact nativeRow_J2
  | J3 => exact J3Cover.nativeRow_J3
  | J4 => exact nativeRow_J4
  | HS => exact nativeRow_HS
  | McL => exact nativeRow_McL
  | He => exact nativeRow_He
  | Ru => exact nativeRow_Ru
  | Suz => exact nativeRow_Suz
  | ONan => exact ONCover.nativeRow_ONan
  | Co1 =>
    exact nativeRow_of_two_one_three_zero rfl (hC _ (by decide)) rowBound_Co1
      two_dvd_card_hopfMultiplier_Co1 kernelTrivialAt_three_Co1 (hBig _ (by decide))
  | Co2 =>
    exact nativeRow_of_two_zero_three_zero rfl (hC _ (by decide)) rowBound_Co2
      kernelTrivialAt_three_Co2 (hBig _ (by decide))
  | Co3 =>
    exact nativeRow_of_two_zero_three_zero rfl (hC _ (by decide)) rowBound_Co3
      kernelTrivialAt_three_Co3 (hBig _ (by decide))
  | Fi22 =>
    exact nativeRow_of_two_one_three_one rfl (hC _ (by decide)) rowBound_Fi22
      two_dvd_card_hopfMultiplier_Fi22 nativeCell3_Fi22 (hBig _ (by decide))
  | Fi23 =>
    exact nativeRow_of_two_zero_three_zero rfl (hC _ (by decide)) rowBound_Fi23 h.fi23_three
      (hBig _ (by decide))
  | Fi24Prime =>
    exact nativeRow_of_two_zero_three_one rfl (hC _ (by decide)) rowBound_Fi24Prime
      (Fi24Three.nativeCell3_Fi24Prime_of_fi23 h.fi23_three) (hBig _ (by decide))
  | HN => exact nativeRow_HN
  | Ly =>
    exact nativeRow_of_two_zero_three_zero rfl (hC _ (by decide)) rowBound_Ly
      kernelTrivialAt_three_Ly (hBig _ (by decide))
  | Th =>
    exact nativeRow_of_two_zero_three_zero rfl (hC _ (by decide)) rowBound_Th
      kernelTrivialAt_three_Th (hBig _ (by decide))
  | B =>
    exact nativeRow_of_two_one_three_zero rfl (hC _ (by decide)) rowBound_B
      two_dvd_card_hopfMultiplier_B
      (UniversalCoverMonster.kernelTrivialAt_three_B_of_fi23_cell h.fi23_three)
      (hBig _ (by decide))
  | M =>
    exact nativeRow_M_of_b_three
      (UniversalCoverMonster.kernelTrivialAt_three_B_of_fi23_cell h.fi23_three)

theorem sporadicMultipliers_of_ledger (hBig : ∀ s, s ≠ .M → BigPrimeFacts s)
    (h : SporadicOpenCells) : SporadicMultipliers :=
  sporadicMultipliers_of_native (nativeSporadicMultipliers_of_ledger hBig h)

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
