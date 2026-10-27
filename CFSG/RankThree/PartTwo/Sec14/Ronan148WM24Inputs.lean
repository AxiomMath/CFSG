module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census219.M24TcData
public meta import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census219.M24TcData
public meta import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThreeCore.M24
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThreeCore.M24
public meta import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.RankThree.Native.FiveKit
public meta import CFSG.RankThree.Native.FiveKit
public import CFSG.Sporadic.Schreier.M24
public meta import CFSG.Sporadic.Schreier.M24

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148W

open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.Monster.B.Mathieu CFSG.AGLEmbeddingD2.Wilson.ThreeCore.M24 CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native
  CFSG.AGLEmbeddingD2.Wilson.Census219

@[expose] def invWords : List (List ℤ) := [
    [1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2, -1, 2, -1, 2, -1, 2, -1, -2, -1, -2, -1, 2, -1,
     2, -1, 2, -1, -2, -1, 2, -1, -1, -2, -1, -2, -1, 2, -1, 2, -1, 2, 2, 1, 2, 1, -2, 1, 2, 1,
     2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 2, -1, -2, -1, 2, -1, 2, -1, -2, -1, 2, 2, 1, 2,
     1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2, 1, -2, 1, -2, 1, -2, 1, 2, 1, -2, 1, -2,
     1, 2, 2, 1, -2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, -2],
    [-2, -1, -2, -1, -2, -1, 2, -1, -2, -1, -2, -1, 2, -1, -2, -1, -2, -1, 2, 2, -1, 2, -1, 2,
     -1, -2, -1, -2, -1, -2, -1, -2, -1, -2, -1, -2, -1, -2, -1, -2, -1, 2, -1, 2, -1, -2, -1,
     -2, -1, -2, -1, -2, -1, -2, -1, -2, -1, 2, -1, 2, -1, 2, -1, 2, -1, 2, 1, 2, 1, 2, 1, 1, 2,
     1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, -1, -2, -1, 2, -1, -2, -1, -2, -1, -2, -1, -2, -1, 2,
     -1, -2, -1, -2, -1, -2, -1, -1, 2, -1, 2, -1, 2, -1, -2, -1, -2, -1, -2, -1, -2, -1, -2, 1,
     2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2,
     1, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, -2],
    [-2, -2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2, 1,
     -2, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1,
     2, 1, 2, 1, -2, 1, -2, 1, -2, -1, 2, -1, -2, -1, 2, -1, -2, -1, -2, -1, 2, -1, -2, -1, -2,
     -1, -2, -1, 2, -1, 2, -1, 2, -1, -2, -1, -2, -1, -2, -1, 2, -1, 2, -1, 2, -1, -2, -1, 2, -1,
     2, -1, -2, -1, -2, -1, -2, -1, -2, -1, 2],
    [-2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 2, -1, 2, -1, -2, -1, 2, -1, -2, -1, -2, -1, 2, -1, 2,
     -1, -2, -1, 2, -1, -2, -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1,
     -2, 1, -2, 1, -2, -1, 2, -1, 2, -1, -2, -1, 2, -1, 2, -1, 2, -1, 2, -1, 2, -1, -2, -1, -2,
     -1, -2, -1, 2, -1, -2, -1, 2, -1, -2, -1, -2, -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2, 1, -2],
    [2, -1, -2, -1, -2, -1, -2, -1, 2, -1, 2, -1, -2, -1, -2, -1, 2, 2, -1, -2, -1, -2, -1, -2,
     -1, -2, -1, -2, -1, -2, -1, 2, -1, -2, -1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1,
     -2, 1, -2, 1, -2, 1, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2,
     1, 2, 1, 2, 1, -2, 1, -2, 1, -2, -1, 2, -1, -2, -1, 2, -1, 2, -1, 2, -1, 2, -1, -2, -1, -2,
     -1, -2, -1, -2, -1, -2, -1, 2, 2, 1, 2, 1, 2, -1, -2, -1, 2, -1, -2, -1, -2, -1, 2, -1, 2,
     -1, -2, -1, -2, -1, 2, -1, -2, -1, 2, -1, -2, -1, 2, -1, -2, -1, -2, -1, 2, -1, 2],
    [-2, -1, 2, -1, -2, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, -2,
     1, -2, 1, -2, 1, 1, 2, -1, 2, -1, 2, -1, 2, -1, -2, -1, -2, -1, 2, -1, 2, -1, 2, -1, -2, -1,
     2, -1, -1, -2, -1, -2, -1, 2, -1, 2, -1, 2, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2,
     1, -2, 1, 2, 1, 2, 1, -2, -1, 2, -1, -2, -1, 2, -1, -2, -1, 2, -1, 2, 2, 1, -2, 1, -2, 1,
     -2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 2, 1, -2, 1, -2, 1, 2, 1, 2,
     1, 2, 1, 1, -2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, -2]]

@[expose] def invArrs (_ : Unit := ()) : Array (Array ℕ) :=
  (invWords.map fun w => natArr (wT w)).toArray

@[expose] def pairArrs (x p : Array ℕ) : List (Array ℕ) :=
  (List.range 3).flatMap fun i => (List.range 3).map fun j =>
    compA 24 (powArr 24 x i) (powArr 24 p j)

@[expose] def invCheck (_ : Unit := ()) : Bool :=
  let Q := invArrs ()
  let C := m24CC ()
  validA 24 m24xA &&
    allLt Q.size (fun l => validA 24 Q[l]! &&
      eqA 24 (conjA 24 Q[l]! m24xA) (invCand 24 m24xA)) &&
    allLt C.pts.size (fun k =>
      let p := C.pts[k]!
      !(eqA 24 (powArr 24 p 3) (idA 24)) ||
        (let E := pairArrs m24xA p
         Q.toList.any fun q => E.any (eqA 24 (conjA 24 q p))))

end CFSG.RankThree.PartTwo.Sec14.Ronan148W
