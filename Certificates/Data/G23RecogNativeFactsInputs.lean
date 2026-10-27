module

public import Certificates.Data.G23RecogNativeInputs
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434G23Words

public section

namespace CFSG.GH74.QTGen4.Recog.G23

open CFSG.RankThree.PartTwo.Census.Carrier.G2Three CFSG.RankThree.PartTwo.Sec4.Item434RemG23

@[expose] def nW : List ℕ := [0, 2, 2, 0, 1, 3, 3, 1]

@[expose] def eWord : Fin 6 → List ℕ := ![
  [1],
  [3],
  nW ++ [0] ++ CFSG.RankThree.PartTwo.Sec4.Item434RemG23.invWord nW,
  nW ++ [2] ++ CFSG.RankThree.PartTwo.Sec4.Item434RemG23.invWord nW,
  [0, 0, 2, 0, 2, 0, 0],
  [0, 1, 0, 6] ++ (nW ++ [2] ++ CFSG.RankThree.PartTwo.Sec4.Item434RemG23.invWord nW) ++ [0, 1, 0]]

@[expose] def x1Word : List (Fin 6 × Bool) :=
  [(4, false), (5, false), (0, false), (4, false), (5, true), (3, true), (5, false), (0, true),
    (5, true), (1, true), (0, true), (3, false), (5, false), (0, false), (5, false), (4, false)]

@[expose] def y1Word : List (Fin 6 × Bool) :=
  [(5, true), (1, false), (5, true), (2, false), (5, true), (0, false), (5, false), (2, false),
    (5, true), (2, false), (5, false), (1, false), (4, true), (0, true)]

end CFSG.GH74.QTGen4.Recog.G23
