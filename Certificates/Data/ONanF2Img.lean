module

public import Certificates.Data.ONanF2Pres
public import Certificates.Data.ChengHeldONImages

public section

namespace CFSG.OddStandard.ONanRec.F2

open CFSG.OddStandard.ChengHeld.ONSylow

@[expose] def alpImgs : Array (Array Nat) := #[
    #[1, 12, 7, 8, 9, 24, 30, 3, 2, 27, 19, 6, 21, 22, 26, 16, 13, 25, 10, 23, 31, 0, 15, 18,
      14, 20, 5, 29, 11, 4, 28, 17],
    #[22, 15, 9, 29, 21, 24, 30, 27, 4, 0, 19, 6, 16, 8, 26, 7, 3, 25, 10, 23, 31, 13, 2, 18,
      14, 20, 5, 1, 11, 12, 28, 17],
    #[22, 15, 9, 29, 21, 31, 23, 27, 4, 0, 5, 19, 16, 8, 25, 7, 3, 11, 26, 24, 30, 13, 2, 14,
      17, 6, 20, 1, 10, 12, 18, 28],
    #[25, 6, 31, 10, 24, 4, 15, 28, 5, 17, 8, 22, 23, 26, 27, 30, 18, 0, 3, 2, 12, 14, 20, 7,
      9, 1, 29, 11, 13, 19, 16, 21],
    #[6, 25, 28, 5, 18, 3, 0, 31, 10, 30, 8, 22, 14, 19, 12, 17, 24, 15, 4, 13, 27, 23, 11, 21,
      16, 1, 29, 20, 2, 26, 9, 7]]

@[expose] def alpInvs : Array (Array Nat) := #[
    #[21, 0, 8, 7, 29, 26, 11, 2, 3, 4, 18, 28, 1, 16, 24, 22, 15, 31, 23, 10, 25, 12, 13, 19,
      5, 17, 14, 9, 30, 27, 6, 20],
    #[9, 27, 22, 16, 8, 26, 11, 15, 13, 2, 18, 28, 29, 21, 24, 1, 12, 31, 23, 10, 25, 4, 0, 19,
      5, 17, 14, 7, 30, 3, 6, 20],
    #[9, 27, 22, 16, 8, 10, 25, 15, 13, 2, 28, 17, 29, 21, 23, 1, 12, 24, 30, 11, 26, 4, 0, 6,
      19, 14, 18, 7, 31, 3, 20, 5],
    #[17, 25, 19, 18, 5, 8, 1, 23, 10, 24, 3, 27, 20, 28, 21, 6, 30, 9, 16, 29, 22, 31, 11, 12,
      4, 0, 13, 14, 7, 26, 15, 2],
    #[6, 25, 28, 5, 18, 3, 0, 31, 10, 30, 8, 22, 14, 19, 12, 17, 24, 15, 4, 13, 27, 23, 11, 21,
      16, 1, 29, 20, 2, 26, 9, 7]]

@[expose] def alpGenWords : List (List (Fin 5 × Bool)) :=
  [[(4, false), (3, true)],
   [(2, true), (1, false), (1, false), (1, false)],
   [(0, true), (0, true), (3, true), (3, true), (0, true), (1, true), (2, false), (3, true),
    (3, true), (0, false)],
   [(2, true), (1, false), (1, false), (0, false)],
   [(0, true), (0, true), (3, true), (0, true), (0, true), (4, true), (3, true)],
   [(0, false), (3, true), (4, false), (0, false), (0, false), (3, false), (0, false),
    (0, false)]]

@[expose] def alpLetL (l : Fin 5 × Bool) : List Nat :=
  (if l.2 then alpImgs[l.1.val]! else alpInvs[l.1.val]!).toList

@[expose] def alpWordL (w : List (Fin 5 × Bool)) : List Nat :=
  w.foldl (fun acc l => compL acc (alpLetL l)) (List.range 32)

@[expose] def alpImgOK : Bool :=
  (List.range 5).all (fun i => isInvL alpImgs[i]!.toList alpInvs[i]!.toList) &&
    alpRels.all (fun w => alpWordL w == List.range 32) &&
    (List.range 6).all (fun j =>
      alpWordL alpGenWords[j]! == CFSG.ONSchreier.Data.T32Chain.generators[j]!.toList) &&
    (List.range 32).any fun x =>
      (alpWordL [(0, true), (0, true), (2, true), (2, true)]).getD x 0 != x

end CFSG.OddStandard.ONanRec.F2
