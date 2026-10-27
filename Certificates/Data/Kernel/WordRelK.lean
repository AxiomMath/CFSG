module

public import CFSG.Monster.B.TwoA.Sp8.P0StructInputs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicBTwoDFixInputs
public import CFSG.Monster.B.TwoA.Sp8.GenActionHom

public section

namespace CFSG.KC.WordRelK

open CFSG.Monster.B CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B.TwoA.Sp8.WordRel
  CFSG.ComponentClassification.RankTwoSporadic.B.TwoDFix

@[expose] def packP (y : Model.Pauli) : Nat :=
  y.2.1 + 4096 * y.2.2 + (bif y.1 then 16777216 else 0)

@[expose] def unpackP (x : Nat) : Model.Pauli :=
  (Nat.beq (x / 16777216 % 2) 1, x % 4096, x / 4096 % 4096)

@[expose] def foldX (k v : Nat) : Nat := v ^^^ (v >>> k)

@[expose] def par12 (v : Nat) : Nat := foldX 1 (foldX 2 (foldX 4 (foldX 8 v))) % 2

@[expose] def mulP (x y : Nat) : Nat :=
  x ^^^ y ^^^ par12 ((y % 4096) &&& (x / 4096 % 4096)) * 16777216

@[expose] def rStarP : Nat := 782336

@[expose] def pcEqP (x y : Nat) : Bool := Nat.beq x y || Nat.beq x (y ^^^ rStarP)

@[expose] def basisP (k : Nat) : Model.Pauli :=
  bif Nat.blt k 12 then (false, 2 ^ k, 0) else (false, 0, 2 ^ (k - 12))

@[expose] def genP (i : Nat) : Nat := packP (pauliGen i)

@[expose] def allBelow (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => ih && f k) n

@[expose] def allL (p : XLetter → Bool) (w : List XLetter) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun ℓ _ ih => p ℓ && ih) w

@[expose] def pauliEq (x y : Model.Pauli) : Bool :=
  (x.1 == y.1) && Nat.beq x.2.1 y.2.1 && Nat.beq x.2.2 y.2.2

@[expose] def letterEq : XLetter → XLetter → Bool
  | .lift k, .lift k' => Nat.beq k k'
  | .pc y, .pc y' => pauliEq y y'
  | .sign a, .sign a' => Nat.beq a a'
  | _, _ => false

@[expose] def tIdx (ℓ : XLetter) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun t _ ih => bif letterEq ℓ t then 0 else ih + 1)
    tLetters

@[expose] def rowIdx : XLetter → Nat
  | .lift k => k
  | ℓ => 43 + tIdx ℓ

@[expose] def okT : XLetter → Bool
  | .lift k => Nat.blt k 43
  | ℓ => Nat.blt (tIdx ℓ) 9

@[expose] def letterAt (r : Nat) : XLetter :=
  bif Nat.blt r 43 then .lift r else tLetters.getD (r - 43) (.lift 0)

@[expose] def rowAt (T r : Nat) : Nat := (T >>> (600 * r)) % 2 ^ 600

@[expose] def entryAt (row k : Nat) : Nat := (row >>> (25 * k)) % 33554432

@[expose] def tabOK (T r : Nat) : Bool :=
  (letterAt r).conjN (true, 0, 0) == (true, 0, 0) &&
    allBelow 24 fun k => unpackP (entryAt (rowAt T r) k) == (letterAt r).conjN (basisP k)

@[expose] def chunkLo (c : Nat) : Nat := [0, 23, 32, 43, 52].getD c 52

@[expose] def tabChunk (T c : Nat) : Bool :=
  allBelow (chunkLo (c + 1) - chunkLo c) fun i => tabOK T (chunkLo c + i)

@[expose] def applyRow (row y : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun acc _ _ => acc)
    (fun _ ih acc yb rb =>
      ih (bif Nat.beq (yb % 2) 1 then mulP acc (rb % 33554432) else acc) (yb / 2)
        (rb / 33554432))
    24 (y / 16777216 * 16777216) (y % 16777216) row

@[expose] def conjW (T : Nat) (w : List XLetter) (y : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) y (fun ℓ _ ih => applyRow (rowAt T (rowIdx ℓ)) ih) w

@[expose] def relT (T : Nat) (w w' : List XLetter) : Bool :=
  allL okT w && allL okT w' &&
    allBelow 23 (fun i => pcEqP (conjW T w (genP i)) (conjW T w' (genP i))) &&
    xTrack w false 0 == xTrack w' false 0

@[expose] def lCommRowT (T i : Nat) : Bool :=
  allBelow 16 fun j => bif Nat.blt i j then
    relT T (lWord (2 ^ i) ++ lWord (2 ^ j))
      (lWord (2 ^ j) ++ lWord (2 ^ i) ++ tWord ((lCommN.getD i []).getD j 0)) else true

@[expose] def lCommSymOK : Bool :=
  allBelow 16 fun i => Nat.beq ((lCommN.getD i []).getD i 0) 0 &&
    allBelow 16 fun j => Nat.beq ((lCommN.getD i []).getD j 0) ((lCommN.getD j []).getD i 0)

@[expose] def lSqT (T i : Nat) : Bool := relT T (lWord (2 ^ i) ++ lWord (2 ^ i)) []

@[expose] def uConjLRowT (T k : Nat) : Bool :=
  allBelow 16 fun j =>
    relT T (uWord k ++ lWord (2 ^ j))
      (lWord ((uConjLN.getD k []).getD j (0, 0)).1 ++ tWord ((uConjLN.getD k []).getD j (0, 0)).2 ++
        uWord k)

@[expose] def uConjTRowT (T k : Nat) : Bool :=
  allBelow 9 fun j =>
    relT T (uWord k ++ tWord (2 ^ j)) (tWord ((uConjTN.getD k []).getD j 0) ++ uWord k)

@[expose] def uSqT (T k : Nat) : Bool :=
  relT T (uWord k ++ uWord k) (lWord (uSqN.getD k (0, 0)).1 ++ tWord (uSqN.getD k (0, 0)).2)

@[expose] def uCommRowT (T j : Nat) : Bool :=
  allBelow 10 fun k => bif Nat.beq j k then true else
    relT T (uWord j ++ uWord k)
      (lWord ((uCommN.getD j []).getD k (0, 0)).1 ++ tWord ((uCommN.getD j []).getD k (0, 0)).2 ++
        uWord k ++ uWord j)

@[expose] def uCommDiagOK : Bool :=
  allBelow 10 fun j => (uCommN.getD j []).getD j (0, 0) == (0, 0)

@[expose] def coDecT (T i : Nat) : Bool :=
  relT T ((coGens.getD i []).map .lift)
    (lWord (coDecN.getD i (0, 0)).1 ++ tWord (coDecN.getD i (0, 0)).2)

@[expose] def paDecT (T i : Nat) : Bool :=
  relT T ((pauliWords.getD i []).map .lift)
    (lWord (paDecN.getD i (0, 0)).1 ++ tWord (paDecN.getD i (0, 0)).2)

@[expose] def lengthsOK : Bool := Nat.beq coGens.length 9 && Nat.beq pauliWords.length 15

end CFSG.KC.WordRelK
