module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront12
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyFiveA
import CFSG.Quasithin.Background.A3ComponentsQuotient
import CFSG.Quasithin.Background.VolIE54
import CFSG.RankThree.PartTwo.Sec15.F153L3C2Quot
import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
import CFSG.Quasithin.Background.B6
import CFSG.Quasithin.Background.B6Example
import CFSG.Quasithin.Background.B6Offenders
import CFSG.Quasithin.Background.E2Hyp
import CFSG.Quasithin.Background.E2SolvTwo
import CFSG.Quasithin.Background.F2Equiv
import CFSG.Quasithin.Background.F9FiveStruct
import CFSG.Quasithin.Background.F9G2
import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
import CFSG.Quasithin.EmptyFaithful.S142Statements
import CFSG.Quasithin.H13.A5S1326
import CFSG.Quasithin.H13.A5Top
import CFSG.Quasithin.Vol2.Ch6Defs
import CFSG.RankThree.PartTwo.Sec14.Std
import CFSG.RankThree.PartTwo.Sec15.F153L3C2Act
import CFSG.RankThree.PartTwo.Sec15.F153L3C2Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.McClurg

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem isQuasisimple_bar2 {M L : Subgroup G} (hL : F12.IsComponentModO2 M L) :
    CFSG.Open.IsQuasisimple (Bar2 L) := by
  obtain ⟨-, -, -, hN, hq⟩ := id hL
  haveI := hN
  have heq : CFSG.pCore 2 ↥L = (pCoreOf 2 M).subgroupOf L := by
    rw [← TwelveTwentyFive.pCoreOf_eq hL]
    exact (Subgroup.comap_map_eq_self_of_injective L.subtype_injective _).symm
  exact CFSG.Quasithin.A3.isQuasisimple_iff_open.mp
    (hq.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq heq))

theorem odd_card_center_bar2 (L : Subgroup G) : Odd (Nat.card (Subgroup.center (Bar2 L))) :=
  CFSG.RankThree.PartTwo.Sec15.F153L3C2.odd_card_center_of_pCore_eq_bot
    CFSG.Quasithin.VolI.E54.pCore_two_quotient_eq_bot

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.McClurg
