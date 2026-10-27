module

public import CFSG.Sporadic.Schreier.CountSpec
public import CFSG.Quasithin.Vol2.KGFactC31ActCheck
public import CFSG.Sporadic.Mathieu.M22

public section

namespace CFSG.Quasithin.KGC31.M22

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu
  CFSG.Certificates CFSG.Quasithin.KGC31.Native

@[expose] def gensT : ℤ → Table := fun l => if l = 1 then toTable m22gA else toTable m22gB

@[expose] def gensG : ℤ → Equiv.Perm (Fin 22) := fun l => if l = 1 then m22gA else m22gB

@[expose] def w5 : List ℤ := [2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1,
    2, 2, 2, 1, 2, 1, 2, 2, 1]

@[expose] def w7 : List ℤ := [1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1,
    2, 1, 2, 2, 1, 2, 2]

@[expose] def w11 : List ℤ := [2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2,
    1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2]

@[expose] def x5T : Table := wordT 22 gensT w5

@[expose] def x7T : Table := wordT 22 gensT w7

@[expose] def x11T : Table := wordT 22 gensT w11

@[expose] def hexW : List (List ℤ) := [[1, 2, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2,
    2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2], [1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2,
    1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1], [2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2,
    2, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2], [2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2,
    2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2]]

@[expose] def duadW : List (List ℤ) := [[2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2,
    1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2], [1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2,
    2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1], [2, 1, 2, 2, 2, 1, 2, 1, 2,
    1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2], [2, 2, 1, 2, 1, 2, 1, 2,
    1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2]]

@[expose] def e8W : List (List ℤ) := [[2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2,
    2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2], [1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2,
    1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2], [1, 2, 2, 2, 1, 2, 2, 1, 2, 1]]

@[expose] def hexConjW : List ℤ := [1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2,
    2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 2]

@[expose] def hexT : List Table := hexW.map (wordT 22 gensT)

@[expose] def duadT : List Table := duadW.map (wordT 22 gensT)

@[expose] def e8T : List Table := e8W.map (wordT 22 gensT)

@[expose] def hexConjT : Table := wordT 22 gensT hexConjW

@[expose] def hex2T : List Table := hexT.map (conjTab 22 hexConjT (invT 22 hexConjT))

@[expose] def cands5 : List (List Table) := [duadT, hexT, hex2T]

@[expose] def cands7 : List (List Table) := [e8T]

@[expose] def hexGenW : List (List ℤ) := [[1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2,
    1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 1], [1, 2, 1, 2, 1, 2, 1, 2, 2, 2, 1,
    2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 1]]

@[expose] def hexChainW : List (List ℤ) := [[1, -2, 1, 1, -2, -1, -2, 1, -2], [-1, -2, -1, -1, -2,
    -1, -1, 2, 2], [1, -2, 1, 1, 2, -1, 2, 1, -2], [1, 2, 2, -1, -1, 2, -1, -2, 1], [2, 1, 1, -2,
    -1, -1, -2], [1, 2, -1, -1, -1, -2]]

@[expose] def hexMasks : List (List ℕ) := [[8, 15, 10, 11], [7, 1, 14, 12]]

@[expose] def duadGenW : List (List ℤ) := [[2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2,
    2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2], [2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2,
    2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1]]

@[expose] def duadChainW : List (List ℤ) := [[-1, 2, -1, 2, 2, -1], [-1, 2, -1, -1, -2], [1, 2, 2,
    1, 2, 1, -2], [2, 2]]

@[expose] def duadMasks : List (List ℕ) := [[4, 8, 9, 14], [1, 2, 5, 10]]

@[expose] def hexGen : List (Equiv.Perm (Fin 22)) := hexGenW.map fun w => tab (wordG gensG w)

@[expose] def duadGen : List (Equiv.Perm (Fin 22)) := duadGenW.map fun w => tab (wordG gensG w)

@[expose] def hexChain : RawSchreierDatum 22 :=
  certificate (by decide) hexGen hexChainW #v[0, 1, 2, 3] (by decide)

@[expose] def duadChain : RawSchreierDatum 22 :=
  certificate (by decide) duadGen duadChainW #v[2, 3, 4] (by decide)

end CFSG.Quasithin.KGC31.M22

end
