module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenRSmall6Lift
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenRSmall6CaseII
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenSixDefs
public import CFSG.RankThree.PartOne.S12.SolTightHolds

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

theorem cardRLeTwo_six :
    CardRLeTwo 6 := by
  intro G _ _ M X S hcat
  obtain ⟨C⟩ := exists_cfg_six S
  obtain ⟨D⟩ := C.exists_piData (by norm_num) (by decide)
  rcases S.inCatalog_or_tight SolSeven.nodeStatement_holds
      CFSG.RankThree.PartOne.SolIn.solomonTimmesfeldTight_holds with h | h
  · exact absurd h hcat
  · exact RSmall6.card_Rc_le_two_six_of_tight C D RSmall6.lemma3Lift_holds
      RSmall6.caseIISix_holds h

end CFSG.RankThree.PartTwo.Sec19.SolEven
