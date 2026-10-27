module

public import CFSG.RankThree.PartTwo.Sec14.Ronan143Q169
public import CFSG.RankThree.PartTwo.Sec16.Item169General

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.PartTwo.Sec15

theorem item169R_of_steps_fiveQ (h1614 : Step1614) (h1616 : Step1616) (h1619 : Step1619)
    (hU38 : Step169U38) (hP : Para1619Five) (h1621 : Step1621) (h1623 : Step1623)
    (hP23 : Para1623) (h1624 : Step1624) (h143 : Ronan148Q.Item143QS14) (h1423 : Item14_23R)
    (hPA : Step169PComm) (h5 : Step169EndFiveL316) (h163 : Item163R) (hMeets : Step163Meets)
    (h1514 : Item1514R) (h1510 : Item1510R) (hBr : Step169TwoBridge) : Item169R := by
  intro G _ _ A c L h
  have h1 := Ronan143Q.rank3II_16_9_1_of_fiveQ h h1614 h1616 h1619 hU38 hP h1621 h1623 hP23
    h1624 h143 h1423 hPA h5
  exact ⟨h1, rank3II_16_9_2_of h h1 (h163 G A c L h) hMeets (h1514 G A c L h)
    (h1510 G A c L h) hBr⟩

end CFSG.RankThree.PartTwo.Sec16
