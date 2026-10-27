module

public import CFSG.RankThree.Co2.XSylowCert
public import CFSG.RankThree.Co2.ClassesCert
public meta import CFSG.RankThree.Co2.XSylowCert
public meta import CFSG.RankThree.Co2.ClassesCert
public meta import CFSG.RankThree.Co2.Rows
public meta import CFSG.Monster.B.TwoA.Co2Inv.ConjCert
public meta import CFSG.Monster.B.TwoA.Co2Inv.Data
public meta import CFSG.Monster.B.TwoA.Census.NatCert
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Matrix

public noncomputable section

namespace CFSG.RankThree.Co2

open CFSG.Monster CFSG.Monster.B.Co2 CFSG.Monster.B.Short CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Census CFSG.Monster.B.TwoA.Co2Inv

@[expose] def xWords9 : Array (List ℕ) := #[
  [6, 41, 38, 35, 0, 27, 5, 7, 27, 9, 6, 13, 8, 9, 8, 10, 17, 20, 1, 5, 19, 6, 25, 17, 5, 20, 6,
    0, 4, 5, 4, 7],
  [29, 26, 0, 8, 40, 37],
  [6, 25, 15, 2, 20, 2, 7, 6, 41, 28, 27, 7, 9, 6, 13, 8, 9, 8, 10, 17, 20, 1, 5, 19, 6, 25, 17,
    5, 20, 6, 5, 5, 8],
  [28, 22, 37, 35, 33]
]

@[expose] def dWord : List ℕ := [32, 31]

@[expose] def f9W : List ℕ := [41, 29, 26, 21, 29, 21, 6, 28, 26, 22, 32, 31, 27, 41, 27, 31, 32,
  22, 26, 28, 11, 6, 20, 27, 38, 28, 29, 38, 23, 25, 27, 41, 35, 33, 32, 39, 36, 21, 25, 24, 39,
  24, 22, 36, 39, 24, 39, 28, 22, 36, 35, 34, 25, 6, 41, 27, 28, 32, 31, 27, 41, 27, 31, 32, 22,
  37, 36, 25, 41]

@[expose] def e1W : List ℕ := [6, 2, 20, 14, 15, 41, 28, 6, 22, 13, 14, 15, 1, 7, 18, 3, 18, 15,
  1, 3, 18, 3, 4, 0, 15, 18, 11, 12, 14, 20, 6, 4, 2, 17, 8, 7, 17, 6, 41, 27, 32, 7, 5, 1, 11,
  10, 6, 20, 6, 10, 11, 1, 5, 7, 27, 26, 25, 21, 7]

end CFSG.RankThree.Co2
