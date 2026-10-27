module

public import CFSG.Quasithin.H13.L32NKGRankInputs

public section

namespace CFSG.Quasithin.H13.KGCert

@[expose] def wT0 : List Bool := [false, false, true, false, false, true]

@[expose] def wT1 : List Bool := [false, true, true, true, true]

@[expose] def t0C : List ℕ := evalWord wT0

@[expose] def t1C : List ℕ := evalWord wT1

@[expose] def g22ConjCheck : Bool :=
  g22Invs.all fun x => g22Elems.any fun y => mulC y x == mulC t0C y || mulC y x == mulC t1C y

end CFSG.Quasithin.H13.KGCert
