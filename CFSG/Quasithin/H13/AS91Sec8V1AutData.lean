module

public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords

public section

namespace CFSG.Quasithin.H13.AS91.M24G

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.Th.Native

@[expose] def sxA : Equiv.Perm (Fin 24) where
  toFun :=
    ![14, 12, 13, 15, 22, 21, 23, 20, 8, 9, 10, 11, 5, 6, 4, 7, 3, 1, 0, 2, 16, 17, 18, 19]
  invFun :=
    ![18, 17, 19, 16, 14, 12, 13, 15, 8, 9, 10, 11, 1, 2, 0, 3, 20, 21, 22, 23, 7, 5, 4, 6]
  left_inv := by decide
  right_inv := by decide

@[expose] def sxB : Equiv.Perm (Fin 24) where
  toFun :=
    ![12, 13, 15, 14, 7, 5, 6, 4, 22, 20, 23, 21, 10, 9, 8, 11, 16, 17, 19, 18, 1, 2, 3, 0]
  invFun :=
    ![23, 20, 21, 22, 7, 5, 6, 4, 14, 13, 12, 15, 0, 1, 3, 2, 16, 17, 19, 18, 9, 11, 8, 10]
  left_inv := by decide
  right_inv := by decide

@[expose] def sxChainWords : List (List ℤ) :=
  [[1, -2, -2, -1], [-1, -3, 2, 2], [4, 4, 3], [-5, -4, -5, 3], [-5, 6, 5],
   [5, -3, -5, -1, -1, 4, 1], [-6, -8, 2, 8, 2],
   [-9, -8, 9, 5, -3, -9, 4, -5, -1, -9, -4, 2]]

@[expose] def sxBase : Vector (Fin 24) 6 := #v[0, 4, 5, 8, 1, 2]

@[expose] def sxAT : Equiv.Perm (Fin 24) := tab sxA

@[expose] def sxBT : Equiv.Perm (Fin 24) := tab sxB

theorem sxAT_eq : sxAT = sxA := tab_eq sxA

theorem sxBT_eq : sxBT = sxB := tab_eq sxB

@[expose] def sxCert : RawSchreierDatum 24 :=
  certificate (by decide) [sxAT, sxBT] sxChainWords sxBase (by decide)

@[expose] def sxAutWords : List (List ℕ × ℕ) :=
  [([0, 1], 12), ([0, 1, 2, 3], 12), ([0, 0, 1, 2, 3], 10), ([0, 1, 1, 2, 1], 12)]

@[expose] def sxCenterOK : Bool :=
  let a := toTable sxAT
  let b := toTable sxBT
  let e := idT 24
  (allTables sxCert).all fun T => !commT 24 T a || !commT 24 T b || tblEq 24 T e

end CFSG.Quasithin.H13.AS91.M24G
