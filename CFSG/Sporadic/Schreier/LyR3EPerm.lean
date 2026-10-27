module

public import CFSG.Sporadic.Schreier.LyPermCheckInputs

public section

namespace CFSG.Sporadic.LySchreier

@[expose] def dImgArr : Array (Array Nat) := #[
  #[0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 8], #[0, 1, 2, 3, 5, 4, 7, 6, 8, 9, 10],
  #[0, 1, 3, 2, 4, 5, 7, 6, 8, 9, 10], #[0, 1, 2, 3, 6, 7, 5, 4, 8, 10, 9],
  #[0, 1, 4, 5, 2, 3, 7, 6, 8, 10, 9], #[2, 3, 0, 1, 4, 5, 7, 6, 8, 10, 9],
  #[1, 0, 3, 2, 5, 4, 7, 6, 8, 9, 10]]

@[expose] def dWord (x : Fin 11) : List Nat :=
  [[], [6], [5], [2, 5], [4, 5], [4, 2, 5], [3, 4, 5], [3, 4, 2, 5], [], [0], [0, 0]][x.val]!

@[expose] def dRep (x : Fin 11) : Fin 11 := if x.val < 8 then 0 else 8

@[expose] def dCand (a b : Fin 11) (x : Fin 11) : Fin 11 :=
  (dWord x).foldr (fun k y => arrFun (dImgArr[k]!) y) (if x.val < 8 then a else b)

theorem dWord_rep :
    ∀ x : Fin 11, (dWord x).foldr (fun k y => arrFun (dImgArr[k]!) y) (dRep x) = x := by
  decide +kernel

theorem dWord_lt : ∀ x : Fin 11, ∀ k ∈ dWord x, k < 7 := by decide +kernel

theorem dCand_check : ∀ a b : Fin 11,
    (∀ k : Fin 7, ∀ x, dCand a b (arrFun (dImgArr[k.val]!) x) =
      arrFun (dImgArr[k.val]!) (dCand a b x)) →
    (∀ x y, dCand a b x = dCand a b y → x = y) →
    (∀ x, dCand a b x = x) ∨ ∀ x, dCand a b x = arrFun (dImgArr[6]!) x := by
  decide +kernel

end CFSG.Sporadic.LySchreier
