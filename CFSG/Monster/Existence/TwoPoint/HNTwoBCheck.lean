module

public import CFSG.Monster.Existence.TwoPoint.HNTwoBData
public import CFSG.Monster.Existence.TwoPoint.HNData
public import CFSG.Monster.Existence.TwoPoint.HNRigid

public section

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.Monster.B.Short

@[expose] def hnXWord : List Native.Gen := [.rho (true, 0, 0)]

@[expose] def hnWW : List Native.Gen := hnWU[0]! ++ hnWU[3]!

@[expose, noinline] def hnTwoBCheck : Bool :=
  (hnXWord ++ hnCW ++ (hnCW ++ hnWW)).all Native.Gen.validB &&
    checkP4 (HS.pw (hnXWord ++ hnCW)) (HS.pw (hnCW ++ hnWW))

theorem hn_wordLin_twoB
    (h : wordLin (hnXWord ++ hnCW) = wordLin (hnCW ++ hnWW)) :
    wordLin hnCW * wordLin hnXWord = wordLin hnWW * wordLin hnCW := by
  rwa [wordLin_append, wordLin_append] at h

end CFSG.Monster.Existence
