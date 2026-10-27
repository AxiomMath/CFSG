module

public import CFSG.RankThree.Co2.Enum
public meta import CFSG.RankThree.Co2.Enum
public meta import CFSG.RankThree.Co2.Rows
public meta import CFSG.Monster.B.TwoA.Co2Inv.ConjCert
public meta import CFSG.Monster.B.TwoA.Co2Inv.Data
public meta import CFSG.Monster.B.TwoA.Census.NatCert
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Matrix

public noncomputable section

namespace CFSG.RankThree.Co2

open CFSG.Monster CFSG.Monster.B.Co2 CFSG.Monster.B.Short CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Census CFSG.Monster.B.TwoA.Co2Inv

@[expose] def piWord : List ℕ :=
  [2, 2, 3, 7, 7, 16, 14, 4, 4, 5, 11, 1, 5, 0, 2, 2, 3, 7, 7, 16, 14, 4, 4, 5, 11, 1, 5, 0,
    2, 2, 3, 7, 7, 16, 14, 4, 4, 5, 11, 1, 5, 0]

@[expose] def repWords : Array (List ℕ) :=
  #[[9], [2], [12], [12, 9], [17, 7, 0, 15, 3, 16, 17, 7, 0, 15, 3, 16], [17], [17, 9],
    piWord, piWord ++ [9], [16, 1, 18, 7, 11, 11, 12, 14]]

@[expose] def classSizes : Array ℕ := #[1, 270, 1260, 1260, 22680, 15120, 15120, 1008, 1008, 120960]

end CFSG.RankThree.Co2
