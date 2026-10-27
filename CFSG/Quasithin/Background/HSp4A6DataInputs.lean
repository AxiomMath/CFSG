module

public import CFSG.Quasithin.Background.HSp4Model
public import CFSG.Quasithin.Background.G6Natural
public meta import Mathlib.Algebra.Field.ZMod
public meta import Mathlib.GroupTheory.Nilpotent
public meta import Mathlib.GroupTheory.Perm.Sign
public meta import Mathlib.Data.Matrix.Block
public meta import Mathlib.Data.Fintype.Perm
public meta import Mathlib.Data.Matrix.Mul
public meta import Mathlib.Data.Fin.VecNotation
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveTauAlg

public section

namespace CFSG.Quasithin

namespace H

namespace Sp4A6

open CFSG.Assembly.LowTwoRank Matrix Equiv

open CFSG.QuasithinUnique.Lin2.Five (tauMat)

open scoped Matrix

@[expose] def bas : Fin 2 ⊕ Fin 2 → Fin 6 → ZMod 2 :=
  Sum.elim ![![1, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 1, 0]] ![![0, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 1]]

@[expose] def dualBas : Fin 2 ⊕ Fin 2 → Fin 6 → ZMod 2 :=
  Sum.elim ![![0, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 1]] ![![1, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 1, 0]]

@[expose] def coord (y : Fin 6 → ZMod 2) : Fin 2 ⊕ Fin 2 → ZMod 2 := fun r => y ⬝ᵥ dualBas r

@[expose] def perm6 (σ : Perm (Fin 6)) (y : Fin 6 → ZMod 2) : Fin 6 → ZMod 2 := fun i => y (σ⁻¹ i)

@[expose] def psiMat (σ : Perm (Fin 6)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2) :=
  Matrix.of fun r c => coord (perm6 σ (bas c)) r

@[expose] def ones : Fin 6 → ZMod 2 := fun _ => 1

@[expose] def cyc345 : Perm (Fin 6) := (Equiv.swap 3 4) * (Equiv.swap 4 5)

end Sp4A6

end H

end CFSG.Quasithin
