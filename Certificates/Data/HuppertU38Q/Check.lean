module

public import Certificates.Data.HuppertU38Q.Data
public import Certificates.Data.HuppertU38.Data
public import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.RankThree.Native.PermEnumeration

public section

namespace U38Sylow

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
  CFSG.RankThree.PartTwo.Sec4.Item434U38

@[expose] def keyPts : List ℕ := base1.toList

@[expose] def qCert (_ : Unit := ()) : ArrCert := enumBfs 513 qGens keyPts 800

@[expose] def cubeOne (a : Array ℕ) : Bool := eqA 513 (compA 513 a (compA 513 a a)) (idA 513)

@[expose] def inX (pts : Array (Array ℕ)) (lev3 : Array Level) : List ℕ :=
  (List.range pts.size).filter fun i => siftA 513 lev3 base3 0 pts[i]!

@[expose] def cosetCubes (r : Array ℕ) (pts : Array (Array ℕ)) (idx : List ℕ) : List (Array ℕ) :=
  (idx.map fun i => compA 513 r pts[i]!).filter cubeOne

@[expose] def noCommuting (A B : List (Array ℕ)) : Bool :=
  A.all fun a => B.all fun b => !eqA 513 (compA 513 a b) (compA 513 b a)

@[expose] def u38SylowCheck (_ : Unit := ()) : Bool :=
  let c := qCert ()
  let lev1 := rawLevels 513 strong1 base1
  let lev3 := rawLevels 513 strong3 base3
  let nIdx := inX c.pts lev3
  enumOK 513 qGens keyPts c && c.pts.size == 729 &&
    allLt qGens.size (fun k => siftA 513 lev1 base1 0 qGens[k]!) && nIdx.length == 81 &&
    noCommuting (cosetCubes qGens[0]! c.pts nIdx) (cosetCubes qGens[1]! c.pts nIdx)

end U38Sylow
