module

public import CFSG.RankThree.PartTwo.Sec13.KF135Chev2Classical
public import CFSG.RankThree.PartTwo.Sec13.KF135Chev2ExcG2E2
public import CFSG.RankThree.PartTwo.Sec13.KF135Chev2ExcD4E2
public import CFSG.RankThree.PartTwo.Sec13.KF135Chev2ExcSz
public import CFSG.RankThree.PartTwo.Sec13.KF135Chev2ExcF4E2
public import CFSG.RankThree.PartTwo.Sec13.KF135Chev2ExcTits

public section

namespace CFSG.RankThree.PartTwo.Sec13.KF135Chev2

open CFSG.RankThree.PartTwo.Sec13.KF135Proof

theorem kF135At_fam7_of (hG2 : KF135At KF135Chev2Exc.Fam7G2)
    (hD4 : KF135At KF135Chev2Exc.Fam7D4) (hSz : KF135At KF135Chev2Exc.Fam7Sz)
    (hF4 : KF135At KF135Chev2Exc.Fam7F4) (hTits : KF135At KF135Chev2Exc.Fam7Tits) :
    KF135At Fam7 := by
  intro S _ _ p P x u V hF h
  rcases hF with hF | hF | hF | hF | hF | hF
  · exact kF135At_fam7Classical S p P x u V hF h
  · exact hG2 S p P x u V hF h
  · exact hD4 S p P x u V hF h
  · exact hSz S p P x u V hF h
  · exact hF4 S p P x u V hF h
  · exact hTits S p P x u V hF h

section Final


theorem kF135At_fam7 : KF135At Fam7 :=
  kF135At_fam7_of KF135Chev2Exc.kF135At_fam7G2 KF135Chev2Exc.kF135At_fam7D4
    KF135Chev2Exc.kF135At_fam7Sz KF135Chev2Exc.kF135At_fam7F4 KF135Chev2Exc.kF135At_fam7Tits

end Final

end CFSG.RankThree.PartTwo.Sec13.KF135Chev2
