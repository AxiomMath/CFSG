module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONCoverMain
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.TripleCoverON
public import Certificates.Certificate291371
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.PrimaryCells
public import Certificates.Certificate24320

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONCover

open CFSG.CosetTable CFSG.Sporadic.Recognition.ONMultiplier

theorem card_hopfMultiplier_J_le_three_of_certificate :
    0 < Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier CFSG.Sporadic.ON.J) ∧
      Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier CFSG.Sporadic.ON.J) ≤ 3 := by
  obtain ⟨h₀, h₂, -⟩ := Certificates.certificate24320
  obtain ⟨h₁, h₃, h₄, h₅⟩ := Certificates.certificate291371
  exact card_hopfMultiplier_le_three h₀ h₁ h₂ h₃ h₄ h₅

theorem card_hopfMultiplier_of_mulEquiv_le_three
    {Y : Type} [Group Y]
    (e : Y ≃* CFSG.Sporadic.ON.J) :
    0 < Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier Y) ∧
      Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier Y) ≤ 3 := by
  have h : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier Y) =
      Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier CFSG.Sporadic.ON.J) :=
    card_hopfMultiplier_eq_of_mulEquiv e
  have h' := card_hopfMultiplier_J_le_three_of_certificate
  exact h ▸ h'

theorem card_hopfMultiplier_nativeON_le_three :
    0 < Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
      (CFSG.Blueprint.NativeSporadic.Carrier .ONan)) ∧
    Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
      (CFSG.Blueprint.NativeSporadic.Carrier .ONan)) ≤ 3 :=
  card_hopfMultiplier_of_mulEquiv_le_three CFSG.Sporadic.ON.onEquivJ

theorem nativeRow_ONan :
    Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
      (CFSG.Blueprint.NativeSporadic.Carrier .ONan)) = 3 := by
  obtain ⟨hpos, hle⟩ := card_hopfMultiplier_nativeON_le_three
  have hdvd := three_dvd_card_hopfMultiplier_ON
  have := Nat.le_of_dvd hpos hdvd
  omega

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONCover
