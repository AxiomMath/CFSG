module

public import CFSG.LieType.Multipliers.G23Data
public import CFSG.Certificates.CosetTableShort
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs

public section

namespace CFSG.CGT.PushingUpLit.CGT6.EmbModule

open CFSG.Sporadic.He.Native CFSG.LieType.Multipliers.G23

@[expose] def prodArr (p d : ℕ) (R : Fin 4 → Array (Array ℕ)) (js : List (Fin 4)) :
    Array (Array ℕ) :=
  js.foldr (fun j M => mulM p d (R j) M) (idM d)

@[expose] def nbW : List (Fin 4) := [0, 2, 2, 0]

@[expose] def nbInvW : List (Fin 4) := [0, 0, 2, 0, 0]

@[expose] def naW : List (Fin 4) := [1, 3, 3, 1]

@[expose] def naInvW : List (Fin 4) := [1, 1, 3, 1, 1]

@[expose] def uW : List (Fin 4) := [1]

@[expose] def vW : List (Fin 4) := nbW ++ uW ++ nbInvW

@[expose] def a1W : List (Fin 4) := naW ++ [0] ++ naInvW

@[expose] def z0W : List (Fin 4) := naW ++ vW ++ naInvW

@[expose] def a2W : List (Fin 4) := nbW ++ a1W ++ nbInvW

@[expose] def cW : List (Fin 4) := [2, 1, 1, 3, 1, 3, 1, 1, 0]

@[expose] def entryOf (M : Array (Array ℕ)) (i j : ℕ) : ℕ := (M[i]!)[j]!

@[expose] def splU : Array (Array ℕ) := rootProd uW

@[expose] def splV : Array (Array ℕ) := rootProd vW

@[expose] def splZ : Array (Array ℕ) := rootProd z0W

@[expose] def splA1 : Array (Array ℕ) := rootProd a1W

@[expose] def splA2 : Array (Array ℕ) := rootProd a2W

@[expose] def splC : Array (Array ℕ) := rootProd cW

@[expose] def splitCheck : Bool :=
  let M := mulM 3 14
  (M splA1 (M splA1 splA1) == idM 14) && (M splA2 (M splA2 splA2) == idM 14) &&
    (M splZ (M splZ splZ) == idM 14) && (M splU (M splU splU) == idM 14) &&
    (M splA1 splA2 == M splA2 splA1) &&
    (M splU splA1 == M splA1 splU) && (M splU splA2 == M splA2 splU) &&
    (M splV splA1 == M splA1 splV) && (M splV splA2 == M splA2 splV) &&
    (M splZ splA1 == M splA1 splZ) && (M splZ splA2 == M splA2 splZ) &&
    (M splU splZ == M splZ splU) && (M splV splZ == M splZ splV) &&
    (M splU splV == M splZ (M splV splU)) &&
    (M splC splA1 == M splA2 splC) && (M splC splA2 == M splA1 (M splA2 splC)) &&
    (entryOf splA1 0 5 == 2) && (entryOf splZ 0 12 == 2)

@[expose] def coverRoot (j : Fin 4) : Array (Array ℕ) := coverWordArr (genWord j)

@[expose] def covU : Array (Array ℕ) := prodArr 2 54 coverRoot uW

@[expose] def covV : Array (Array ℕ) := prodArr 2 54 coverRoot vW

@[expose] def covA1 : Array (Array ℕ) := prodArr 2 54 coverRoot a1W

@[expose] def covA2 : Array (Array ℕ) := prodArr 2 54 coverRoot a2W

@[expose] def covC0 : Array (Array ℕ) :=
  mulM 2 54 covU (mulM 2 54 covA2 (mulM 2 54 (mulM 2 54 covU covU) (mulM 2 54 covA2 covA2)))

@[expose] def coverEmbCheck : Bool :=
  let M := mulM 2 54
  (M covA1 (M covA1 covA1) == idM 54) && (M covA2 (M covA2 covA2) == idM 54) &&
    (M covU (M covU covU) == idM 54) && (M covC0 (M covC0 covC0) == idM 54) &&
    (M covC0 covU == M covU covC0) && (M covC0 covV == M covV covC0) &&
    (M covC0 covA1 == M covA1 covC0) && (M covC0 covA2 == M covA2 covC0) &&
    (M covA1 covA2 == M covA2 covA1) && (M covV covA2 == M covA2 covV) &&
    (M covU covA2 == M covC0 (M covA2 covU)) &&
    (M covV covA1 == M covC0 (M covC0 (M covA1 covV))) &&
    (entryOf covC0 0 1 == 1)

end CFSG.CGT.PushingUpLit.CGT6.EmbModule
