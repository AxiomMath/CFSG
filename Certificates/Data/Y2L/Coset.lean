module

public import Certificates.Data.Y2L.Words
public import CFSG.Certificates.CosetTablePresented
public import Mathlib

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec2

@[expose] def y2l_cosetCheck (n : ℕ) (e : Bool) (cap N : ℕ) : Bool :=
  CFSG.CosetTable.check
    (CFSG.CosetTable.presParams (y2l_ws26 n e) (([] : List (Fin 5)).map fun x => [(x, true)]))
    cap N

end CFSG.OddStandard.HigherRank.G2Three.Sec2
