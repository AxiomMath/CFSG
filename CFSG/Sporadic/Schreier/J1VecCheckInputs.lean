module

public import CFSG.Sporadic.Schreier.J1CertData
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.J1ModelTransport
public meta import CFSG.Sporadic.Schreier.J1CertData
public meta import CFSG.LocalAnalysis.ProperTwoGeneratedCore.J1ModelTransport
public meta import CFSG.Open.Defs
public import CFSG.Open.Defs

public section

namespace CFSG.Sporadic.Schreier

open CFSG.ProperTwoGeneratedCore Matrix

@[expose] def j1Idx (l : List ℕ) (i : Fin 3080) : Fin 3080 :=
  ⟨l.getD i 0 % 3080, Nat.mod_lt _ (by norm_num)⟩

@[expose] def j1BasisMat : Matrix (Fin 7) (Fin 7) (ZMod 11) :=
  Matrix.of fun r c => j1Vec (Fin.castLE (by norm_num) c) r

@[expose] def j1BasisInv : Matrix (Fin 7) (Fin 7) (ZMod 11) :=
  !![0, 5, 8, 7, 7, 1, 6;
     3, 5, 9, 4, 4, 3, 7;
     1, 3, 2, 1, 5, 1, 3;
     7, 9, 3, 0, 1, 1, 2;
     1, 1, 4, 1, 4, 9, 6;
     6, 1, 4, 10, 7, 4, 3;
     3, 9, 6, 0, 1, 3, 4]

end CFSG.Sporadic.Schreier
