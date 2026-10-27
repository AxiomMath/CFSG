module

public import CFSG.Monster.Existence.ELevelCheck

public section

namespace CFSG.Monster.Existence

open CFSG.Monster.B.TwoA.Census

@[expose] def fullOK (sl : List ℕ) (i : ℕ) : Bool :=
  let tt := tT i
  let td := tD i
  rankOKT tt td i && checkX sl tt td (packP (wP i))

@[expose] def allOK : Bool :=
  let sl := shortPacked
  fullOK sl 1 && fullOK sl 2 && fullOK sl 6

end CFSG.Monster.Existence
