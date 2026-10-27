module

public import Certificates.Data.HuppertU38Three.Data
public import Certificates.Data.HuppertU38Q.NoE81
public import CFSG.RankThree.PartOne.KS.PKit
public import CFSG.RankThree.PartOne.KS.PKitLines
public import Mathlib

public section

namespace U38Three

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
  CFSG.RankThree.PartTwo.Sec4.Item434U38 CFSG.RankThree.PartOne U38Sylow

@[expose] def fix01 (a : Array ℕ) : Bool := a[0]! == 0 && a[1]! == 1

@[expose] def rels3 : List (ℕ × ℕ × ℕ) := [(0, 0, 1), (1, 1, 1), (2, 2, 1)]

@[expose] def keyPts9 : List ℕ := [0, 1, 2]

@[expose] def hCert (_ : Unit := ()) : ArrCert := enumBfs 513 hGens keyPts 400

@[expose] def lCert (_ : Unit := ()) : ArrCert := enumBfs 513 #[la, lb] keyPts 600

@[expose] def cCert (_ : Unit := ()) : ArrCert := enumBfs 513 cGens keyPts 1600

@[expose] def pCert (_ : Unit := ()) : ArrCert := enumBfs 9 #[pa, pb] keyPts9 600

@[expose] def cubeIdx (pts : Array (Array ℕ)) : List ℕ :=
  (List.range pts.size).filter fun j => cubeOne pts[j]!

@[expose] def hElemCheck (pts : Array (Array ℕ)) (d e : Array ℕ) : Bool :=
  let cs := cubeIdx pts
  cs.all fun i => eqA 513 pts[i]! (idA 513) || eqA 513 pts[i]! d || eqA 513 pts[i]! e ||
    (commAt pts[i]! d && decide ((cs.filter fun j => commAt pts[i]! pts[j]!).length ≤ 9))

@[expose] def conjGensM (n m : ℕ) (c : ArrCert) (k : ℕ) : Array (Array ℕ) :=
  Array.ofFn (n := m) fun j => conjA n c.pts[j.val]! c.pts[k]!

@[expose] def conjPointOKM (n m : ℕ) (ps : List ℕ) (c : ArrCert) (k : ℕ) (ck : ArrCert) : Bool :=
  enumOK n (conjGensM n m c k) ps ck && ck.pts.size == c.pts.size

@[expose] def conjSimpleOKM (n m : ℕ) (ps : List ℕ) (c : ArrCert) : Bool :=
  decide (m ≤ c.pts.size) && allLt c.pts.size fun k => eqA n c.pts[k]! (idA n) ||
    conjPointOKM n m ps c k (enumBfs n (conjGensM n m c k) ps (c.pts.size + 1))

@[expose] def hCheck (_ : Unit := ()) : Bool :=
  let c := hCert ()
  let lev1 := rawLevels 513 strong1 base1
  enumOK 513 hGens keyPts c && c.pts.size == 378 &&
    allLt hGens.size (fun k => siftA 513 lev1 base1 0 hGens[k]! && fix01 hGens[k]!) &&
    validA 513 d0 && siftA 513 lev1 base1 0 d0 && fix01 d0 && cubeOne d0 && !eqA 513 d0 (idA 513) &&
    hElemCheck c.pts d0 (compA 513 d0 d0)

@[expose] def memPts (c : ArrCert) (x : Array ℕ) : Bool := c.pts.toList.any (eqA 513 x)

@[expose] def lCheck (_ : Unit := ()) : Bool :=
  let c := lCert ()
  let lev3 := rawLevels 513 strong3 base3
  enumOK 513 #[la, lb] keyPts c && c.pts.size == 504 &&
    siftA 513 lev3 base3 0 la && siftA 513 lev3 base3 0 lb && commAt la d0 && commAt lb d0 &&
    centOKP 3 513 strong3 base3 d0 rels3 cGens keyPts (cCert ()) 1512 &&
    allLt cGens.size (fun k => memPts c (conjA 513 cGens[k]! la) && memPts c (conjA 513 cGens[k]! lb) &&
      memPts c (conjInvA 513 cGens[k]! la) && memPts c (conjInvA 513 cGens[k]! lb))

@[expose] def pCheck (_ : Unit := ()) : Bool :=
  let c := pCert ()
  allLt 9 (fun j => la[j]! == pa[j]! && lb[j]! == pb[j]!) &&
    enumOK 9 #[pa, pb] keyPts9 c && c.pts.size == 504 && conjSimpleOKM 9 12 keyPts9 c

@[expose] def u38ThreeCheck (_ : Unit := ()) : Bool := hCheck () && lCheck () && pCheck ()

end U38Three
