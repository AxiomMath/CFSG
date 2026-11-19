
module

public import CFSG.Sporadic.Th.Max3.DataBase

@[expose] public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3

def abLetterRows (l : ℤ) : Array V4 :=
  if l = 1 ∨ l = -1 then rowsA else if l = 2 then rowsB else mulRows rowsB rowsB

def signedRows (letter : ℤ → Array V4) (w : List ℤ) : Array V4 :=
  prodRows (w.map letter)

def abRows (w : List ℤ) : Array V4 := signedRows abLetterRows w

end CFSG.Sporadic.ThSchreier
