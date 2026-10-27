
module

public import CFSG.Sporadic.Th.Max3.DataBase

@[expose] public section

namespace CFSG.Sporadic.Th.Max3.AllConj

open CFSG.Sporadic.Th.Native

@[expose] def invLetter (i : ℕ) : List ℕ :=
  if i = 1 then [1] else [2, 2]

@[expose] def invWord (w : List ℕ) : List ℕ :=
  w.reverse.flatMap invLetter

end CFSG.Sporadic.Th.Max3.AllConj

namespace CFSG.Sporadic.Th.Max3

open CFSG.Sporadic.Th.Native

@[expose] def fusionWordQ0 : List ℕ := [1, 2, 2, 1, 2]

@[expose] def fusionWordX : List ℕ := [2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2]

end CFSG.Sporadic.Th.Max3

namespace CFSG.Sporadic.Th.Max3.AllConj

open CFSG.Sporadic.Th.Native

@[expose] def abLetterRows (i : ℕ) : Array V4 :=
  if i = 1 then rowsA else rowsB

@[expose] def abRows (w : List ℕ) : Array V4 :=
  prodRows (w.map abLetterRows)

@[expose] def fusionRows (rg rgi rr : Array V4) : Array V4 :=
  mulRows (powRows (mulRows (mulRows (mulRows rgi rr) rg) rowsA) 9) rgi

@[expose] def rowsFusionX : Array V4 :=
  fusionRows (abRows fusionWordX) (abRows (invWord fusionWordX)) rowsX

end CFSG.Sporadic.Th.Max3.AllConj
