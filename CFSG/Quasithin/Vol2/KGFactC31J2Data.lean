module

public import CFSG.Sporadic.Schreier.PairJ2CheckInputs
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutNative
public import CFSG.Sporadic.Schreier.PairJ2CertBase

public section

namespace CFSG.Quasithin.KGC31.J2

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative
  CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.J2Cover

@[expose] def genTab (j : ℕ) : Table :=
  Array.ofFn (n := 315) fun i => UInt32.ofNat ((j2StrongArrs[j]!)[i.val]!)

@[expose] def gensT : ℤ → Table := fun l => if l = 1 then genTab 0 else genTab 1

@[expose] noncomputable def gensG : ℤ → Equiv.Perm (Fin 315) :=
  fun l => if l = 1 then j2Gen 0 else j2Gen 1

@[expose] def w5a : List ℤ :=
  [1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1,
    2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1]

@[expose] def w5b : List ℤ :=
  [2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1,
    2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1]

@[expose] def w7 : List ℤ :=
  [2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1,
    2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2,
    1, 2, 2]

@[expose] def invTabs : List Table :=
  filterProducts 315 (ordTest 315 2) (chainTables 315 j2StrongArrs PairJ2.baseArr) (idT 315) []

@[expose] def x5aT : Table := wordT 315 gensT w5a

@[expose] def x5bT : Table := wordT 315 gensT w5b

@[expose] def x7T : Table := wordT 315 gensT w7

end CFSG.Quasithin.KGC31.J2

end
