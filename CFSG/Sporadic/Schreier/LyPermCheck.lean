module

public import Certificates.Data.CFSGNative.LySchreier.Data
public meta import Certificates.Data.CFSGNative.LySchreier.Data
public import CFSG.Sporadic.Schreier.LyPermCheckInputs
public import Certificates.Certificate2186

public section

namespace CFSG.Sporadic.LySchreier

open Native

@[expose] def sImgArr : Array (Array Nat) := #[
  #[2, 3, 0, 1, 4, 5, 6, 7, 8, 9, 10], #[1, 0, 3, 2, 4, 5, 6, 7, 8, 9, 10],
  #[4, 5, 6, 7, 0, 1, 2, 3, 8, 9, 10], #[1, 0, 2, 3, 5, 4, 6, 7, 8, 9, 10],
  #[1, 0, 2, 3, 4, 5, 6, 7, 9, 8, 10]]

@[expose] def sCand (a b c : Fin 11) (x : Fin 11) : Fin 11 :=
  let w : List Nat := [[], [1], [0], [1, 0], [2], [2, 1], [2, 0], [2, 1, 0], [], [4], []][x.val]!
  let r : Fin 11 := if x.val < 8 then a else if x.val < 10 then b else c
  w.foldr (fun k y => arrFun (sImgArr[k]!) y) r

theorem sCand_check : ∀ a b c : Fin 11,
    (∀ k : Fin 5, ∀ x, sCand a b c (arrFun (sImgArr[k.val]!) x) =
      arrFun (sImgArr[k.val]!) (sCand a b c x)) →
    (∀ x y, sCand a b c x = sCand a b c y → x = y) →
    ∀ x, sCand a b c (sCand a b c x) = x := by
  decide +kernel

@[expose] def sWord (x : Fin 11) : List Nat :=
  [[], [1], [0], [1, 0], [2], [2, 1], [2, 0], [2, 1, 0], [], [4], []][x.val]!

@[expose] def sRep (x : Fin 11) : Fin 11 := if x.val < 8 then 0 else if x.val < 10 then 8 else 10

theorem sWord_rep :
    ∀ x : Fin 11, (sWord x).foldr (fun k y => arrFun (sImgArr[k]!) y) (sRep x) = x := by
  decide +kernel

theorem sCand_eq (a b c : Fin 11) (x : Fin 11) :
    sCand a b c x = (sWord x).foldr (fun k y => arrFun (sImgArr[k]!) y)
      (if x.val < 8 then a else if x.val < 10 then b else c) := rfl

@[expose] def qWordL (x : Fin 11) : List Nat :=
  [[], [2, 2], [2, 1], [0], [2], [0, 3, 0], [1], [3, 0], [], [], []][x.val]!

@[expose] def qRep (x : Fin 11) : Fin 11 :=
  if x.val < 8 then 0 else if x.val = 8 then 8 else if x.val = 9 then 9 else 10

theorem qWord_rep :
    ∀ x : Fin 11, (qWordL x).foldr (fun k y => arrFun (qImgArr[k]!) y) (qRep x) = x := by
  decide +kernel

theorem qWord_lt : ∀ x : Fin 11, ∀ k ∈ qWordL x, k < 4 := by decide +kernel

theorem sWord_lt : ∀ x : Fin 11, ∀ k ∈ sWord x, k < 5 := by decide +kernel

theorem qCand_eq (a b c d : Fin 11) (x : Fin 11) :
    qCand a b c d x = (qWordL x).foldr (fun k y => arrFun (qImgArr[k]!) y)
      (if x.val < 8 then a else if x.val = 8 then b else if x.val = 9 then c else d) := rfl

theorem qCand_check : ∀ a b c d : Fin 11,
    (∀ j : Fin 4, ∀ x, qCand a b c d (arrFun (qImgArr[j.val]!) x) =
      arrFun (qImgArr[j.val]!) (qCand a b c d x)) →
    (∀ x y, qCand a b c d x = qCand a b c d y → x = y) →
    ∃ m : Fin 12, ∀ x, qCand a b c d x = arrFun (qNaturalCentralizer[m.val]!) x :=
  Certificates.certificate2186

end CFSG.Sporadic.LySchreier
