module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.J3CoverMain
public import Certificates.Certificate291370
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.PrimaryCells

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.J3Cover

open CFSG.CosetTable
open CFSG.Sporadic.J3.Native (j3Data)

theorem card_hopfMultiplier_J_of_certificate :
    Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (CFSG.Sporadic.J3.J j3Data)) = 3 := by
  obtain ⟨h₁, h₂, h₃⟩ := Certificates.certificate291370
  exact card_hopfMultiplier_J h₁ h₂ h₃

theorem card_hopfMultiplier_of_mulEquiv_J
    {Y : Type} [Group Y] (e : Y ≃* CFSG.Sporadic.J3.J j3Data) :
    Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier Y) = 3 := by
  have h : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier Y) =
      Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (CFSG.Sporadic.J3.J j3Data)) :=
    card_hopfMultiplier_eq_of_mulEquiv e
  have h' := card_hopfMultiplier_J_of_certificate
  exact h.trans h'

theorem card_hopfMultiplier_nativeJ3 :
    Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
      CFSG.Blueprint.NativeSporadic.J3) = 3 := by
  exact card_hopfMultiplier_of_mulEquiv_J CFSG.Sporadic.Bridge.J3.nativeEquiv

theorem nativeRow_J3 :
    Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
      (CFSG.Blueprint.NativeSporadic.Carrier .J3)) = 3 := by
  exact card_hopfMultiplier_nativeJ3

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.J3Cover
