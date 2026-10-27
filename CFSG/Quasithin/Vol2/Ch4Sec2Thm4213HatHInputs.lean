module

public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213HatChk
public import CFSG.Monster.B.Co2.BFS
public import CFSG.Sporadic.HeldB.Common

public section

namespace CFSG.Quasithin.H13.Ch4.HatH

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.Sporadic.HeldB CFSG.Quasithin.H13.Ch4.HatChk

@[expose] def p0Words : List (List ℕ) :=
  [[4, 1, 4, 5, 4, 1, 4, 1], [5, 1, 3, 4, 3, 8, 1, 4, 5], [4, 1, 3, 8, 3, 1, 4]]

@[expose] def d0Word : List ℕ := [5, 3, 4, 8, 3, 1, 4, 8, 1]

@[expose] def p1Words : List (List ℕ) :=
  [[1, 8, 8, 3, 8, 3, 8, 2], [2, 8, 2, 3, 8, 3, 1], [2, 1, 2, 1, 8, 3, 8, 3], [8, 8, 2, 3, 1]]

@[expose] def d1Word : List ℕ := [2, 1, 8, 1, 2, 8, 3, 8, 3, 2]

end CFSG.Quasithin.H13.Ch4.HatH
