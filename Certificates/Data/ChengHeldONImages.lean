module

public import Certificates.Data.ChengHeldONRels
public import CFSG.Sporadic.Schreier.ONOuterData
public import Mathlib.Init

public section

namespace CFSG.OddStandard.ChengHeld.ONSylow

@[expose] def onImgs : Array (Array Nat) := #[
    #[4, 9, 13, 15, 3, 17, 18, 22, 16, 8, 24, 23, 27, 12, 20, 0, 1, 6, 5, 14, 28, 29, 21, 26, 25,
      30, 31, 2, 19, 7, 10, 11],
    #[0, 1, 2, 3, 4, 6, 5, 7, 8, 9, 25, 26, 12, 13, 28, 15, 16, 18, 17, 20, 19, 21, 22, 31, 30,
      10, 11, 27, 14, 29, 24, 23],
    #[13, 22, 4, 27, 12, 19, 20, 9, 29, 21, 11, 25, 15, 3, 18, 2, 7, 14, 28, 6, 5, 16, 8, 30, 23,
      26, 10, 0, 17, 1, 31, 24],
    #[10, 18, 31, 25, 24, 9, 16, 20, 17, 5, 0, 13, 23, 11, 29, 30, 6, 8, 1, 21, 7, 19, 28, 12, 4,
      3, 27, 26, 22, 14, 15, 2],
    #[25, 14, 31, 10, 30, 7, 21, 5, 28, 20, 3, 13, 23, 11, 1, 24, 19, 22, 29, 16, 9, 6, 17, 12,
      15, 0, 27, 26, 8, 18, 4, 2],
    #[5, 10, 14, 6, 17, 0, 3, 23, 25, 24, 1, 29, 28, 20, 2, 18, 30, 4, 15, 27, 13, 31, 26, 7, 9,
      8, 22, 19, 12, 11, 16, 21],
    #[27, 1, 4, 13, 2, 19, 20, 21, 8, 9, 10, 26, 15, 3, 17, 12, 16, 14, 28, 5, 6, 7, 29, 31, 24,
      25, 11, 0, 18, 22, 30, 23],
    #[16, 15, 29, 9, 8, 5, 6, 27, 4, 3, 24, 23, 22, 21, 28, 1, 0, 18, 17, 19, 20, 13, 12, 11, 10,
      30, 31, 7, 14, 2, 25, 26]]

@[expose] def onInvs : Array (Array Nat) := #[
    #[15, 16, 27, 4, 0, 18, 17, 29, 9, 1, 30, 31, 13, 2, 19, 3, 8, 5, 6, 28, 14, 22, 7, 11, 10,
      24, 23, 12, 20, 21, 25, 26],
    #[0, 1, 2, 3, 4, 6, 5, 7, 8, 9, 25, 26, 12, 13, 28, 15, 16, 18, 17, 20, 19, 21, 22, 31, 30,
      10, 11, 27, 14, 29, 24, 23],
    #[27, 29, 15, 13, 2, 20, 19, 16, 22, 7, 26, 10, 4, 0, 17, 12, 21, 28, 14, 5, 6, 9, 1, 24, 31,
      11, 25, 3, 18, 8, 23, 30],
    #[10, 18, 31, 25, 24, 9, 16, 20, 17, 5, 0, 13, 23, 11, 29, 30, 6, 8, 1, 21, 7, 19, 28, 12, 4,
      3, 27, 26, 22, 14, 15, 2],
    #[25, 14, 31, 10, 30, 7, 21, 5, 28, 20, 3, 13, 23, 11, 1, 24, 19, 22, 29, 16, 9, 6, 17, 12,
      15, 0, 27, 26, 8, 18, 4, 2],
    #[5, 10, 14, 6, 17, 0, 3, 23, 25, 24, 1, 29, 28, 20, 2, 18, 30, 4, 15, 27, 13, 31, 26, 7, 9,
      8, 22, 19, 12, 11, 16, 21],
    #[27, 1, 4, 13, 2, 19, 20, 21, 8, 9, 10, 26, 15, 3, 17, 12, 16, 14, 28, 5, 6, 7, 29, 31, 24,
      25, 11, 0, 18, 22, 30, 23],
    #[16, 15, 29, 9, 8, 5, 6, 27, 4, 3, 24, 23, 22, 21, 28, 1, 0, 18, 17, 19, 20, 13, 12, 11, 10,
      30, 31, 7, 14, 2, 25, 26]]

@[expose] def onGenWords : List (List (Fin 8 × Bool)) :=
  [[(0, true), (1, true), (7, true)],
   [(6, true), (3, true), (4, true), (0, false)],
   [(3, true), (6, true), (4, true)],
   [(0, true)],
   [(5, true), (1, true)],
   [(2, true), (5, true), (6, true)]]

@[expose] def compL (t u : List Nat) : List Nat := u.map fun i => t.getD i 0

@[expose] def letL (l : Fin 8 × Bool) : List Nat :=
  (if l.2 then onImgs[l.1.val]! else onInvs[l.1.val]!).toList

@[expose] def wordL (w : List (Fin 8 × Bool)) : List Nat :=
  w.foldl (fun acc l => compL acc (letL l)) (List.range 32)

@[expose] def isInvL (t r : List Nat) : Bool :=
  t.length == 32 && r.length == 32 && (List.range 32).all fun i =>
    decide (t.getD i 0 < 32) && r.getD (t.getD i 0) 0 == i

@[expose] def onImgOK : Bool :=
  (List.range 8).all (fun i => isInvL onImgs[i]!.toList onInvs[i]!.toList) &&
    onRels.all (fun w => wordL w == List.range 32) &&
    (List.range 6).all fun j =>
      wordL onGenWords[j]! == CFSG.ONSchreier.Data.T32Chain.generators[j]!.toList

end CFSG.OddStandard.ChengHeld.ONSylow
