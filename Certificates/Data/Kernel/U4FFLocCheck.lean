module

public import Certificates.Data.Kernel.U4FFLoc
public import CFSG.HardMathSupport.U4FF.ClassLocCheck

public section

namespace CFSG.KC.U4FFLoc

open CFSG.HardMathSupport.U4FF

@[expose] def packL : List ℕ → ℕ
  | [] => 0
  | c :: C => 2 ^ 128 * packL C + c

@[expose] def unpackL : ℕ → ℕ → List ℕ
  | 0, _ => []
  | m + 1, X => X % 2 ^ 128 :: unpackL m (X / 2 ^ 128)

@[expose] def mulPgo (X M : ℕ) : List ℕ → ℕ → ℕ
  | [], _ => 0
  | a :: A, t => a * ((X >>> t) &&& M) ^^^ mulPgo X M A (t + 1)

@[expose] def mulPL (A B : List ℕ) : List ℕ :=
  if (decide (A.length ≤ 128) && A.all (fun a => decide (a < 2 ^ 128)) &&
      B.all (fun c => decide (c < 2 ^ 128))) = true then
    unpackL B.length (mulPgo (packL B) (packL (List.replicate B.length 1)) A 0)
  else mulL A B

@[expose] def hwEncK : List FK → ℕ
  | [] => 0
  | K :: fs => hwOf K + K.dim * hwEncK fs

@[expose] def all44 (p : Fin 4 → Fin 4 → Bool) : Bool :=
  (List.finRange 4).all fun i => (List.finRange 4).all fun j => p i j

@[expose] def piL (n : ℕ) (D : LocData) : List ℕ :=
  addL (mulPL D.bcols.toList D.pmcols.toList) (mulPL [D.z] (zrowL n D.zeta))

@[expose] def yL (fs : List FK) (D : LocData) : ℕ := applyL D.pmcols.toList (1 <<< hwEncK fs)

@[expose] def loc1K (fs : List FK) (m : ℕ) (D : LocData) : Bool :=
  D.bcols.toList.length == m && D.pmcols.toList.length == dimL fs &&
  mulPL D.pmcols.toList D.bcols.toList == oneL m &&
  applyL D.pmcols.toList D.z == 0 &&
  mulPL (zrowL (dimL fs) D.zeta) D.bcols.toList == zeroL m &&
  applyL (piL (dimL fs) D) D.z == D.z &&
  all44 (fun i j => decide (i ≠ j → (List.range (fs.length + 1)).all (fun r =>
    mulPL (piL (dimL fs) D) (mulPL (tabDK fs i j r) D.bcols.toList) ==
      mulPL (tabDK fs i j r) D.bcols.toList) = true)) &&
  all44 (fun i j => decide (i ≠ j → (List.range (fs.length + 1)).all (fun r =>
    applyL (tabDK fs i j r) D.z == if r = 0 then D.z else 0) = true)) &&
  applyL (piL (dimL fs) D) (1 <<< hwEncK fs) == 1 <<< hwEncK fs &&
  all44 (fun i j => decide (i < j → (List.range (fs.length + 1)).all (fun r =>
    decide (1 ≤ r → applyL (tabDK fs i j r) (1 <<< hwEncK fs) = 0)) = true)) &&
  (List.range m).any (fun i => (yL fs D).testBit i)

@[expose] def elemL (fs : List FK) (i j : Fin 4) : List ℕ :=
  (List.range (fs.length + 1)).foldl (fun acc r => addL acc (tabDK fs i j r)) (zeroL (dimL fs))

@[expose] def locOpL (D : LocData) (A : List ℕ) : List ℕ :=
  mulPL D.pmcols.toList (mulPL A D.bcols.toList)

@[expose] def a1L (fs : List FK) : List ℕ := addL (elemL fs 0 3) (oneL (dimL fs))

@[expose] def a2L (fs : List FK) : List ℕ :=
  addL (mulPL (elemL fs 0 2) (elemL fs 1 3)) (oneL (dimL fs))

@[expose] def rankOKK (m : ℕ) (M : List ℕ) (R : RankData) : Bool :=
  M.length == m && R.x.toList.length == R.r && R.y.toList.length == m &&
  R.xl.toList.length == m && R.yr.toList.length == R.r && M == mulPL R.x.toList R.y.toList &&
  mulPL R.xl.toList (mulPL M R.yr.toList) == oneL R.r

@[expose] def loc2K (fs : List FK) (m f1 : ℕ) (D : LocData) : Bool :=
  rankOKK m (locOpL D (a1L fs)) D.rk1 && rankOKK m (locOpL D (a2L fs)) D.rk2 &&
  2 * D.rk1.r + f1 == m && decide (D.rk1.r ≤ D.rk2.r) && decide (2 * D.rk2.r ≤ m)

@[expose] def dlocL (fs : List FK) (D : LocData) (i j : Fin 4) (r : ℕ) : List ℕ :=
  mulPL D.pmcols.toList (mulPL (tabDK fs i j r) D.bcols.toList)

@[expose] def loc3K (fs : List FK) (m : ℕ) (D : LocData) (fsR : List FK) (mR : ℕ)
    (DR : LocData) : Bool :=
  D.pic.toList.length == mR && D.pir.toList.length == m && D.ioc.toList.length == m &&
  D.iol.toList.length == mR &&
  mulPL D.pic.toList D.pir.toList == oneL m && mulPL D.iol.toList D.ioc.toList == oneL m &&
  applyL D.pic.toList (yL fsR DR) == yL fs D &&
  all44 (fun i j => decide (j < i → (List.range 4).all (fun r =>
    mulPL D.pic.toList (dlocL fsR DR i j r) == mulPL (dlocL fs D i j r) D.pic.toList &&
    mulPL D.ioc.toList (dlocL fs D i j r) == mulPL (dlocL fsR DR i j r) D.ioc.toList) = true))

@[expose] def LocValid1K (a b c : Bool) : Bool := loc1K (fsOf a b c) (locM a b c) (locData a b c)

@[expose] def LocValid2K (a b c : Bool) : Bool :=
  loc2K (fsOf a b c) (locM a b c) (locF1 a b c) (locData a b c)

@[expose] def LocValid3K (a b c : Bool) : Bool :=
  loc3K (fsOf a b c) (locM a b c) (locData a b c) (fsOf true true true) (locM true true true)
    (locData true true true)

@[expose] def LocValidK (a b c : Bool) : Bool :=
  LocValid1K a b c && LocValid2K a b c && LocValid3K a b c

end CFSG.KC.U4FFLoc
