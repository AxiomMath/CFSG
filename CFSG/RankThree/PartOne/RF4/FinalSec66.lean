module

public import CFSG.RankThree.PartOne.RF4.Descent
public import CFSG.RankThree.PartOne.S11c.Sec66F4Ree

public section

namespace CFSG.RankThree.PartOne.RF4

open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag

theorem largeReeFieldAutCoset :
    CFSG.RankThree.PartOne.Sec66T.LargeReeFieldAutCoset := by
  intro a _ K _ _ _ hK p hp _ β hβ α hα hx
  exact largeRee_fieldAut_coset_conj a hK hp β hβ α hα hx

end CFSG.RankThree.PartOne.RF4
