module

public import Certificates.Data.CFSGNative.LySchreier.Data
public meta import Certificates.Data.CFSGNative.LySchreier.Data

public section

namespace CFSG.Sporadic.LySchreier

open Native

@[expose] def arrFun (A : Array Nat) (x : Fin 11) : Fin 11 :=
  ⟨A[x.val]! % 11, Nat.mod_lt _ (by decide)⟩

@[expose] def qImgArr : Array (Array Nat) := #[
  #[3, 2, 1, 0, 6, 7, 4, 5, 8, 9, 10], #[6, 7, 5, 4, 3, 2, 0, 1, 8, 9, 10],
  #[4, 5, 7, 6, 1, 0, 2, 3, 8, 9, 10], #[4, 5, 6, 7, 1, 0, 3, 2, 8, 9, 10]]

@[expose] def qCand (a b c d : Fin 11) (x : Fin 11) : Fin 11 :=
  let w : List Nat := [[], [2, 2], [2, 1], [0], [2], [0, 3, 0], [1], [3, 0], [], [], []][x.val]!
  let r : Fin 11 := if x.val < 8 then a else if x.val = 8 then b else if x.val = 9 then c else d
  w.foldr (fun k y => arrFun (qImgArr[k]!) y) r

end CFSG.Sporadic.LySchreier
