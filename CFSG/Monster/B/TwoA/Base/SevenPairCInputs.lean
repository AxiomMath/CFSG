
module

public import CFSG.Monster.B.TwoA.Base.SevenPairB
public meta import CFSG.Monster.B.TwoA.Census.NatCert

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster.Code CFSG.Monster.B.TwoA.Census CFSG.Sporadic.Mathieu

open scoped Pointwise

@[expose] def decMat (n m : ℕ) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  Matrix.of fun i j => if m.testBit (n * i + j) then 1 else 0

@[expose] def codeMat (n : ℕ) (A : Matrix (Fin n) (Fin n) (ZMod 2)) : ℕ :=
  ∑ i : Fin n, ∑ j : Fin n, (A i j).val * 2 ^ (n * i.val + j.val)

@[expose] def matW2 (k : ℕ) : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  if k = 0 then !![1, 1; 0, 1] else !![0, 1; 1, 0]

@[expose] def matW3 (k : ℕ) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  if k = 0 then !![1, 0, 1; 0, 1, 0; 0, 0, 1] else
  if k = 1 then !![1, 0, 0; 0, 1, 1; 0, 0, 1] else
  if k = 2 then !![1, 1, 0; 0, 1, 0; 0, 0, 1] else
  if k = 3 then !![1, 0, 0; 0, 0, 1; 0, 1, 0] else !![0, 1, 0; 1, 0, 0; 0, 0, 1]

@[expose] def actW2 (k m : ℕ) : ℕ := codeMat 2 (matW2 k * decMat 2 m)

@[expose] def actW3 (k m : ℕ) : ℕ := codeMat 3 (matW3 k * decMat 3 m)

@[expose] def glCert2 : NatCert := natBfs actW2 2 (codeMat 2 1) 100

@[expose] def glCert3 : NatCert := natBfs actW3 5 (codeMat 3 1) 1000

end CFSG.Monster.B.TwoA
