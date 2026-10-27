module

public import CFSG.Sporadic.HeldB.AutData
public import CFSG.Sporadic.HeldB.Common

public noncomputable section

namespace CFSG.Sporadic.HeldB

@[expose] def heCentW1 : List ℤ :=
  [-2, 2, 2, -2, -2, -2, -2, 2, 2, 2, 1, 2, 3, -2, -1, -2, -2, -2, 2, 2, 2, 2, -2, -2, 2, 3,
  -2, 2, 2, -2, -2, -2, -2, 2, 2, 2, 1, 2, 3, -2, -1, -2, -2, -2, 2, 2, 2, 2, -2, -2, 2, 3, -2,
  2, 2, -2, -2, -2, -2, 2, 2, 2, 1, 2, 3, -2, -1, -2, -2, -2, 2, 2, 2, 2, -2, -2, 2, 3, -2, 2,
  2, -2, -2, -2, -2, 2, 2, 2, 1, 2, 3, -2, -1, -2, -2, -2, 2, 2, 2, 2, -2, -2, 2, 3, -2, 2, 2,
  -2, -2, -2, -2, 2, 2, 2, 1, 2, 3, -2, -1, -2, -2, -2, 2, 2, 2, 2, -2, -2, 2, 3, -2, 2, 2, -2,
  -2, -2, -2, 2, 2, 2, 1, 2, 3, -2, -1, -2, -2, -2, 2, 2, 2, 2, -2, -2, 2, 3, -2, 2, 2, -2, -2,
  -2, -2, 2, 2, 2, 1, 2, 3, -2, -1, -2, -2, -2, 2, 2, 2, 2, -2, -2, 2, 3, -2, 2, 2, -2, -2, -2,
  -2, 2, 2, 2, 1, 2]

@[expose] def heCentW2 : List ℤ :=
  [-2, 2, 1, 1, 1, -2, 1, 2, -2, 1, -2, -2, 3, 2, 2, -1, 2, -2, -1, 2, -1, -1, -1, -2, 2, 3,
  -2, 2, 1, 1, 1, -2, 1, 2, -2, 1, -2, -2, 3, 2, 2, -1, 2, -2, -1, 2, -1, -1, -1, -2, 2, 3, -2,
  2, 1, 1, 1, -2, 1, 2, -2, 1, -2, -2, 3, 2, 2, -1, 2, -2, -1, 2, -1, -1, -1, -2, 2, 3, -2, 2,
  1, 1, 1, -2, 1, 2, -2, 1, -2, -2, 3, 2, 2, -1, 2, -2, -1, 2, -1, -1, -1, -2, 2, 3, -2, 2, 1,
  1, 1, -2, 1, 2, -2, 1, -2, -2, 3, 2, 2, -1, 2, -2, -1, 2, -1, -1, -1, -2, 2, 3, -2, 2, 1, 1,
  1, -2, 1, 2, -2, 1, -2, -2, 3, 2, 2, -1, 2, -2, -1, 2, -1, -1, -1, -2, 2, 3, -2, 2, 1, 1, 1,
  -2, 1, 2, -2, 1, -2, -2, 3, 2, 2, -1, 2, -2, -1, 2, -1, -1, -1, -2, 2, 3, -2, 2, 1, 1, 1, -2,
  1, 2, -2, 1, -2, -2, 3, 2, 2, -1, 2, -2, -1, 2, -1, -1, -1, -2, 2, 3, -2, 2, 1, 1, 1, -2, 1,
  2, -2, 1, -2, -2, 3, 2, 2, -1, 2, -2, -1, 2, -1, -1, -1, -2, 2, 3, -2, 2, 1, 1, 1, -2, 1, 2,
  -2, 1, -2, -2, 3, 2, 2, -1, 2, -2, -1, 2, -1, -1, -1, -2, 2, 3, -2, 2, 1, 1, 1, -2, 1, 2, -2,
  1, -2, -2]

@[expose] def heDerivedV : List (List ℤ) :=
  [[1, 2, 2, 2, 1, 2, 1, 2, 2, 1],
    [2, 1, 2, 1, 2, 1, 2, 2, 1, 2],
    [1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1]]

@[expose] def hePerfRecords : List (ℕ × List ℤ) :=
  [(0, []), (0, [1, 2, 2, 2, 1, 2, 1, 2, 2, 1])]

@[expose] def heOuterLetters : List (Equiv.Perm (Fin 8330)) := [heGenPerm 0, heGenPerm 1, heAutU]

@[expose, irreducible] def heOuterC1 : Equiv.Perm (Fin 8330) :=
  evalSignedWord heOuterLetters heCentW1

@[expose, irreducible] def heOuterC2 : Equiv.Perm (Fin 8330) :=
  evalSignedWord heOuterLetters heCentW2

@[expose] def heOuterC : Subgroup (Equiv.Perm (Fin 8330)) := Subgroup.closure {heOuterC1, heOuterC2}

@[expose, irreducible] def heOuterDGen (j : ℕ) : Equiv.Perm (Fin 8330) :=
  evalSignedWord [heOuterC1, heOuterC2] (heDerivedV.getD j [])

@[expose] def heOuterD : Subgroup (Equiv.Perm (Fin 8330)) :=
  Subgroup.closure {heOuterDGen 0, heOuterDGen 1, heOuterDGen 2}

end CFSG.Sporadic.HeldB
