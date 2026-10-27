module

public import CFSG.RankThree.PartTwo.Sec4.Census.TripleCoverLiftCert
public import Certificates.Certificate8097
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG.SectionRank CFSG.SectionRank.Native TauCeti

section F2

theorem co3Lift_check : LiftData.check (ops2 22) co3Lift = true :=
  Certificates.certificate8097.1

theorem co2Lift_check : LiftData.check (ops2 22) co2Lift = true :=
  Certificates.certificate8097.2.1

theorem thLift_check : LiftData.check (ops2 248) thLift = true :=
  Certificates.certificate8097.2.2

end F2

theorem co3Lift_covers : liftCovers co3Lift = true := by decide

theorem co2Lift_covers : liftCovers co2Lift = true := by decide

theorem thLift_covers : liftCovers thLift = true := by decide

theorem tripleCoverSporadicRankFour_Co3 :
    TripleCoverSporadicRankFour .Co3 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Co3.nonempty_mulEquiv
  exact LiftCert.tripleCoverSporadicRankFour_of_check (spec2 22) co3Lift co3Lift_check
    co3Lift_covers b

theorem tripleCoverSporadicRankFour_Co2 :
    TripleCoverSporadicRankFour .Co2 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Co2.nonempty_mulEquiv
  exact LiftCert.tripleCoverSporadicRankFour_of_check (spec2 22) co2Lift co2Lift_check
    co2Lift_covers b

theorem tripleCoverSporadicRankFour_Th :
    TripleCoverSporadicRankFour .Th := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Th.nonempty_mulEquiv
  exact LiftCert.tripleCoverSporadicRankFour_of_check (spec2 248) thLift thLift_check
    thLift_covers b

end CFSG.RankThree.PartTwo.Sec4.Census
