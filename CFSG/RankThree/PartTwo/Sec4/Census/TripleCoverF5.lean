module

public import CFSG.RankThree.PartTwo.Sec4.Census.TripleCoverLiftCert
public import Certificates.Certificate8098
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG.SectionRank CFSG.SectionRank.Native TauCeti

section F5

theorem lyLift_check : LiftData.check (opsP 5 111) lyLift = true :=
  Certificates.certificate8098.1

theorem hnLift_check : LiftData.check (opsP 5 133) hnLift = true :=
  Certificates.certificate8098.2

end F5

theorem lyLift_covers : liftCovers lyLift = true := by decide

theorem hnLift_covers : liftCovers hnLift = true := by decide

theorem tripleCoverSporadicRankFour_Ly :
    TripleCoverSporadicRankFour .Ly := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Ly.nonempty_mulEquiv
  exact LiftCert.tripleCoverSporadicRankFour_of_check (specP 5 111) lyLift lyLift_check
    lyLift_covers b

theorem tripleCoverSporadicRankFour_HN :
    TripleCoverSporadicRankFour .HN := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.HN.nonempty_mulEquiv
  exact LiftCert.tripleCoverSporadicRankFour_of_check (specP 5 133) hnLift hnLift_check
    hnLift_covers b

end CFSG.RankThree.PartTwo.Sec4.Census
