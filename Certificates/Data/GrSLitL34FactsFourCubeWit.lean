module

public import Certificates.Data.GrSLitL34FactsFourCubeData
public import CFSG.RankThree.Native.HSMcLFiveCheckInputs
public import CFSG.Sporadic.Schreier.ONOuterData

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts.FourCube

open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native

@[expose] def wordArr {k : ℕ} (n : ℕ) (gs : Array (Array ℕ)) (w : List (Fin k × Bool)) :
    Array ℕ :=
  w.foldl (fun acc l => compA n acc (if l.2 then gs[l.1.val]! else invCand n gs[l.1.val]!)) (idA n)

@[expose] def hsWit : Array (Array ℕ) := #[
    #[45, 71, 29, 94, 96, 19, 6, 50, 74, 60, 83, 34, 75, 5, 61, 15, 16, 68, 37, 76, 86, 18, 93, 65, 9,
      33, 51, 7, 54, 47, 84, 43, 97, 25, 31, 0, 38, 92, 36, 85, 10, 41, 40, 11, 1, 73, 59, 99, 30, 44,
      81, 23, 72, 32, 70, 46, 53, 57, 91, 88, 64, 14, 80, 28, 24, 26, 90, 22, 66, 20, 63, 49, 52, 35, 79,
      12, 13, 69, 67, 89, 4, 27, 82, 42, 98, 3, 77, 87, 55, 8, 17, 58, 21, 78, 39, 95, 62, 56, 48, 2],
    #[68, 34, 65, 46, 73, 54, 87, 62, 47, 24, 74, 39, 52, 28, 61, 6, 15, 27, 13, 70, 86, 76, 37, 10, 64,
      33, 42, 96, 67, 26, 98, 3, 56, 25, 85, 17, 91, 5, 58, 88, 8, 57, 89, 94, 11, 66, 71, 51, 84, 43,
      80, 40, 12, 97, 22, 1, 32, 95, 38, 49, 9, 14, 0, 78, 60, 83, 50, 18, 7, 20, 93, 31, 75, 90, 99,
      72, 63, 69, 21, 2, 45, 4, 41, 79, 48, 55, 77, 16, 44, 29, 81, 36, 19, 92, 59, 82, 35, 53, 30, 23],
    #[70, 2, 68, 42, 13, 39, 15, 92, 73, 24, 96, 23, 36, 94, 33, 16, 87, 22, 43, 85, 20, 31, 44, 27, 64,
      14, 50, 37, 59, 66, 98, 26, 97, 61, 65, 54, 12, 11, 75, 10, 4, 41, 80, 51, 99, 63, 89, 90, 84, 47,
      21, 81, 91, 32, 88, 79, 53, 57, 72, 8, 9, 25, 19, 46, 60, 7, 78, 49, 93, 69, 55, 29, 58, 28, 35,
      38, 3, 77, 71, 0, 76, 18, 82, 62, 48, 83, 86, 6, 74, 45, 67, 52, 34, 1, 40, 95, 5, 56, 30, 17],
    #[26, 99, 2, 96, 76, 94, 77, 89, 92, 9, 85, 88, 38, 13, 84, 69, 20, 71, 28, 40, 16, 73, 49, 55, 60,
      30, 0, 46, 18, 68, 25, 35, 32, 98, 74, 31, 36, 59, 12, 39, 19, 95, 62, 54, 44, 50, 27, 93, 61, 22,
      45, 70, 58, 53, 43, 23, 56, 57, 52, 37, 24, 48, 42, 81, 64, 79, 66, 67, 29, 15, 51, 17, 72, 21, 34,
      75, 4, 6, 90, 65, 80, 63, 82, 83, 14, 10, 87, 86, 11, 7, 78, 91, 8, 47, 5, 41, 3, 97, 33, 1],
    #[11, 42, 3, 2, 99, 90, 61, 35, 26, 32, 49, 0, 75, 44, 16, 33, 14, 40, 89, 71, 69, 28, 94, 79, 53,
      87, 8, 55, 21, 62, 48, 73, 9, 15, 88, 7, 38, 70, 36, 47, 17, 95, 1, 46, 13, 81, 43, 39, 30, 10,
      59, 63, 58, 24, 65, 27, 64, 82, 52, 50, 97, 6, 29, 51, 56, 54, 83, 96, 76, 20, 37, 19, 91, 31, 92,
      12, 68, 86, 85, 23, 93, 45, 57, 66, 98, 78, 77, 25, 34, 18, 5, 72, 74, 80, 22, 41, 67, 60, 84, 4]]

@[expose] def hsKeys : List ℕ := [0, 1, 2, 3, 4]

@[noinline, expose] def hsWitOK : Bool :=
  hsWit.size == 5 && allLt 5 (fun i => validA 100 hsWit[i]!) &&
    allLt 5 (fun i => siftA 100 hs100PLevels hs100BaseArr 0 hsWit[i]!) &&
    (qRels 0).all (fun w => eqA 100 (wordArr 100 hsWit w) (idA 100)) &&
    (let c := enumBfs 100 hsWit hsKeys 600
     enumOK 100 hsWit hsKeys c && c.pts.size == 512)

@[expose] def t32Gens : Array (Array ℕ) := CFSG.ONSchreier.Data.T32Chain.generators

@[expose] def onWitWords : List (List (Fin 6 × Bool)) :=
  [[(0, true), (2, true), (3, true), (0, true)],
    [(0, true), (1, true), (2, true), (5, true), (0, true), (4, true)],
    [(3, true), (4, true), (2, true), (4, true)], [(3, true), (4, true)], [(0, true)]]

@[expose] def onWit : Array (Array ℕ) := (onWitWords.map (wordArr 32 t32Gens)).toArray

@[expose] def onKeys : List ℕ := [0, 5, 1]

@[noinline, expose] def onWitOK : Bool :=
  t32Gens.size == 6 && allLt 6 (fun j => validA 32 t32Gens[j]!) && onWit.size == 5 &&
    allLt 5 (fun i => validA 32 onWit[i]!) &&
    (qRels d1).all (fun w => eqA 32 (wordArr 32 onWit w) (idA 32)) &&
    (let c := enumBfs 32 onWit onKeys 600
     enumOK 32 onWit onKeys c && c.pts.size == 512)

@[noinline, expose] def fourCubeWitOK : Bool := hsWitOK && onWitOK

end CFSG.ComponentClassification.GrSLit.L34Facts.FourCube
