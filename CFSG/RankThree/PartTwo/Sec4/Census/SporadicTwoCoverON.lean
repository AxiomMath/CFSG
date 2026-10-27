module

public import CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverRanks
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import Certificates.Certificate8094
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native
open CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverLift
open CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverRanks
open CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverRanks.Native
open CFSG.RankThree.PartTwo.Sec4.Census.SporadicTwoCover.Native

namespace SporadicTwoCover

theorem on_e8_check : e8Check (ops3 154) onE8Data = true :=
  Certificates.certificate8094

theorem on_e8Datum :
    ∃ a₁ a₂ a₃ n : NativeSporadic.ON, E8Datum a₁ a₂ a₃ n :=
  e8Datum_of_check (spec3 154) onE8Data on_e8_check

end SporadicTwoCover

theorem noRankThreeTwoCover_on :
    NoRankThreeTwoCover NativeSporadic.ON := by
  obtain ⟨a₁, a₂, a₃, n, h⟩ := SporadicTwoCover.on_e8Datum
  exact noRankThreeTwoCover_of_datum h

end CFSG.RankThree.PartTwo.Sec4.Census
