module

public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Data45
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Check3
public meta import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Data45
public meta import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Check3

public section

namespace CFSG.RankThree.PartTwo.Sec4.Sporadic.J2

open CFSG.ComponentClassification.J2Cover CFSG.Certificates.Native CFSG.Monster.B.Co2.Native
  CFSG.RankThree.Native CFSG.Monster.B.Mathieu

@[expose] def gensNaArr : Array (Array ℕ) := gensCaArr.push h1Arr

@[expose] def gensNVArr : Array (Array ℕ) := gensCvArr.push hVArr

@[expose] def vkArr (k i : ℕ) : Array ℕ :=
  conjA 315 cConj[k]! (if i = 1 then v1Arr else v2Arr)

@[expose] def gensS (k : ℕ) : Array (Array ℕ) :=
  let p := if k = 0 then (0, 1) else if k = 1 then (0, 2) else (1, 2)
  #[vkArr p.1 1, vkArr p.1 2, vkArr p.2 1, vkArr p.2 2]

@[expose] def cCa : CFSG.Monster.B.Fischer.ArrCert := enumBfs 315 gensCaArr keyPts 100

@[expose] def cNa : CFSG.Monster.B.Fischer.ArrCert := enumBfs 315 gensNaArr keyPts 200

@[expose] def cCv : CFSG.Monster.B.Fischer.ArrCert := enumBfs 315 gensCvArr keyPts 500

@[expose] def cNV : CFSG.Monster.B.Fischer.ArrCert := enumBfs 315 gensNVArr keyPts 1000

@[expose] def gensNE : Array (Array ℕ) := #[xArr, neGens[0]!, neGens[1]!]

@[expose] def cNE : CFSG.Monster.B.Fischer.ArrCert := enumBfs 315 gensNE keyPts 100

@[expose] def cS (k : ℕ) : CFSG.Monster.B.Fischer.ArrCert := enumBfs 315 (gensS k) keyPts 200

@[expose] def inV (t : Array ℕ) : Bool :=
  eqA 315 t (idA 315) || eqA 315 t v1Arr || eqA 315 t v2Arr || eqA 315 t (compA 315 v1Arr v2Arr)

@[expose] def isTwo8A (t : Array ℕ) : Bool := eqA 315 (sqIterA 8 t) (idA 315)

@[expose] def aElts : List (Array ℕ) :=
  (List.range 3).flatMap fun a => (List.range 3).map fun c =>
    compA 315 (powArr 315 zArr a) (powArr 315 xArr c)

@[expose] def o3Sets : Array (Array ℕ) := o3Pts.map fun p => #[p]

@[expose] def chkElts45 : Bool :=
  allLt gensCaArr.size (fun k => okA gensCaArr[k]! && commA gensCaArr[k]! xArr) &&
    okA h1Arr && eqA 315 (conjA 315 h1Arr xArr) (compA 315 xArr xArr) &&
    okA v1Arr && okA v2Arr && allLt gensCvArr.size (fun k => okA gensCvArr[k]!) &&
    allLt gensCvArr.size (fun k => commA gensCvArr[k]! v1Arr && commA gensCvArr[k]! v2Arr) &&
    okA hVArr && eqA 315 (conjA 315 hVArr v1Arr) v2Arr &&
    eqA 315 (conjA 315 hVArr v2Arr) (compA 315 v1Arr v2Arr) &&
    okA p0Arr && validA 315 outerArr && allLt cConj.size (fun k => okA cConj[k]!) &&
    allLt wGens.size (fun k => okA wGens[k]!) && allLt u34Gens.size (fun k => okA u34Gens[k]!) &&
    allLt neGens.size (fun k => okA neGens[k]! && inE 0 (conjA 315 neGens[k]! zArr) &&
      inE 0 (conjA 315 neGens[k]! xArr)) &&
    !(commA (commutatorA 315 neGens[0]! neGens[1]!) zArr &&
      commA (commutatorA 315 neGens[0]! neGens[1]!) xArr)

@[expose] def chkEnum45 : Bool :=
  enumOK 315 gensCaArr keyPts cCa && cCa.pts.size == 36 &&
    enumOK 315 gensNaArr keyPts cNa && cNa.pts.size == 72 &&
    enumOK 315 gensCvArr keyPts cCv && cCv.pts.size == 240 &&
    enumOK 315 gensNVArr keyPts cNV && cNV.pts.size == 720 &&
    enumOK 315 gensNE keyPts cNE && cNE.pts.size == 54 &&
    [0, 1, 2].all fun k => enumOK 315 (gensS k) keyPts (cS k) && (cS k).pts.size == 64

@[expose] def chkCent45 : Bool :=
  allLt 315 fun a => allLt 160 fun b => allLt 12 fun c =>
    let t := prod3 315 autLevels a b c
    (!(commA t xArr) || inCert cCa t) && (!(commA t v1Arr) || inCert cCv t)

@[expose] def twoTest (ns : Array (Array ℕ)) (w : Array ℕ) : Bool :=
  isTwoA w && ns.all fun n => isTwoA (compA 315 w (conjA 315 n w))

@[expose] def twoTest8 (ns : Array (Array ℕ)) (w : Array ℕ) : Bool :=
  isTwo8A w && ns.all fun n => isTwo8A (compA 315 w (conjA 315 n w))

@[expose] def chkLocal45 : Bool :=
  (allLt cCa.pts.size fun k => !(isTwoA cCa.pts[k]!) || inV cCa.pts[k]!) &&
    inCert cCa v1Arr && inCert cCa v2Arr && commA v1Arr v2Arr &&
    eqA 315 (compA 315 v1Arr v1Arr) (idA 315) && eqA 315 (compA 315 v2Arr v2Arr) (idA 315) &&
    !(eqA 315 v1Arr (idA 315)) && !(eqA 315 v2Arr (idA 315)) && !(eqA 315 v1Arr v2Arr) &&
    o3Sets.size == 3 && setsOK o3Sets 1 && b4Sets.size == 4 && setsOK b4Sets 3 &&
    (allLt cNa.pts.size fun k => permutesSets o3Sets cNa.pts[k]! &&
      permutesSets b4Sets cNa.pts[k]! &&
      (!(fixesSets o3Sets cNa.pts[k]! && fixesSets b4Sets cNa.pts[k]!) ||
        eqA 315 cNa.pts[k]! (idA 315))) &&
    (allLt gensNaArr.size fun k => actsBy o3Sets gensNaArr[k]! (sig3.getD k []) &&
      actsBy b4Sets gensNaArr[k]! (sig4.getD k [])) &&
    (allLt cNa.pts.size fun k => !(twoTest gensNaArr cNa.pts[k]!) || inV cNa.pts[k]!) &&
    (allLt cNV.pts.size fun k => !(twoTest gensNVArr cNV.pts[k]!) || inV cNV.pts[k]!) &&
    (eqA 315 (conjA 315 p0Arr (conjA 315 outerArr xArr)) xArr ||
      eqA 315 (conjA 315 p0Arr (conjA 315 outerArr xArr)) (compA 315 xArr xArr)) &&
    (allLt cNa.pts.size fun k =>
      !(twoTest8 gensNaArr (compA 315 cNa.pts[k]! (compA 315 p0Arr outerArr))))

@[expose] def wg (i j : ℕ) : Array ℕ := wGens[2 * i + j]!

@[expose] def wElts (i : ℕ) : List (Array ℕ) :=
  [idA 315, wg i 0, wg i 1, compA 315 (wg i 0) (wg i 1)]

@[expose] def inW (i : ℕ) (t : Array ℕ) : Bool := (wElts i).any (eqA 315 t)

@[expose] def inWZ (i : ℕ) (t : Array ℕ) : Bool :=
  (wElts i).any fun w => (List.range 3).any fun e =>
    eqA 315 t (compA 315 w (powArr 315 zArr e))

@[expose] def isInvolA (t : Array ℕ) : Bool :=
  eqA 315 (compA 315 t t) (idA 315) && !(eqA 315 t (idA 315))

@[expose] def chkW : Bool :=
  ([0, 1, 2].all fun i =>
      isInvolA (wg i 0) && isInvolA (wg i 1) && commA (wg i 0) (wg i 1) &&
        !(eqA 315 (wg i 0) (wg i 1)) && commA (wg i 0) zArr && commA (wg i 1) zArr &&
        (aElts.all fun f => (wElts i).all fun w => inW i (conjA 315 f w)) &&
        ((wElts i).all fun u => eqA 315 u (idA 315) ||
          ((aElts.any fun f => eqA 315 (conjA 315 f u) (wg i 0)) &&
            (aElts.any fun f => eqA 315 (conjA 315 f u) (wg i 1)))) &&
        ([0, 1, 2].all fun j => j == i || !(inW j (wg i 0)))) &&
    (allLt cCz.pts.size fun k =>
      let t := cCz.pts[k]!
      (!(isInvolA t && aElts.all fun f => commA t (conjA 315 f t)) ||
          inW 0 t || inW 1 t || inW 2 t) &&
        [0, 1, 2].all fun i => !(commA t (wg i 0) && commA t (wg i 1)) || inWZ i t)

@[expose] def inVk (k : ℕ) (t : Array ℕ) : Bool := inV (conjInvA 315 cConj[k]! t)

@[expose] def sA (a : ℕ) : Array ℕ :=
  compA 315 (powArr 315 u34Gens[0]! (a % 2)) (powArr 315 u34Gens[1]! (a / 2))

@[expose] def tB (b : ℕ) : Array ℕ :=
  compA 315 (powArr 315 u34Gens[2]! (b % 2)) (powArr 315 u34Gens[3]! (b / 2))

@[expose] def wC (c : ℕ) : Array ℕ :=
  compA 315 (powArr 315 (commutatorA 315 u34Gens[0]! u34Gens[2]!) (c % 2))
    (powArr 315 (commutatorA 315 u34Gens[0]! u34Gens[3]!) (c / 2))

@[expose] def phiA (a b c : ℕ) : Array ℕ := compA 315 (sA a) (compA 315 (tB b) (wC c))

@[expose] def mulCode4 (x y : ℕ) : ℕ :=
  ((x % 2) * (y % 2) + (x / 2) * (y / 2)) % 2 +
    2 * (((x % 2) * (y / 2) + (x / 2) * (y % 2) + (x / 2) * (y / 2)) % 2)

@[expose] def chkSConj : Bool :=
  [0, 1, 2].all fun i =>
    inCert cP3 cConj[i]! &&
      eqA 315 (conjA 315 cConj[i]! xArr) (compA 315 (powArr 315 zArr i) xArr)

@[expose] def chkSPieces : Bool :=
  [(0, 0), (1, 2), (2, 1)].all fun p => inCert (cS p.1) (wg p.2 0) && inCert (cS p.1) (wg p.2 1)

@[expose] def chkSNorm : Bool :=
  [0, 1, 2].all fun k => (gensS k).all fun s =>
    inCert (cS k) (conjA 315 zArr s) && inCert (cS k) (conjA 315 xArr s)

@[expose] def chkSVWits : Bool :=
  (List.range vWitPairs.length).all fun m =>
    let i := (vWitPairs.getD m (0, 0)).1
    let k := (vWitPairs.getD m (0, 0)).2
    inW i vWits[4 * m]! && inVk k vWits[4 * m + 1]! && inW i vWits[4 * m + 2]! &&
      inVk k vWits[4 * m + 3]! &&
      !(isTwoA (compA 315 vWits[4 * m]! (compA 315 vWits[4 * m + 1]!
        (compA 315 vWits[4 * m + 2]! vWits[4 * m + 3]!))))

@[expose] def chkSTrip : Bool :=
  inVk 0 tripWit[0]! && inVk 1 tripWit[1]! && inVk 2 tripWit[2]! &&
    !(isTwoA (compA 315 tripWit[0]! (compA 315 tripWit[1]! tripWit[2]!)))

@[expose] def chkSDistinct : Bool :=
  !(inCert (cS 1) (vkArr 1 1)) && !(inCert (cS 2) (vkArr 0 1)) && !(inCert (cS 0) (vkArr 2 1))

@[expose] def chkSCz : Bool :=
  allLt (cS 0).pts.size fun k => !(commA (cS 0).pts[k]! zArr) || inW 0 (cS 0).pts[k]!

@[expose] def chkSProd : Bool :=
  allLt (cS 0).pts.size fun k => (wElts 0).any fun w =>
    (List.range 4).any fun e => (List.range 4).any fun f =>
      eqA 315 (cS 0).pts[k]! (compA 315 w (compA 315
        (conjA 315 cConj[0]! (if e = 0 then idA 315 else if e = 1 then v1Arr else
          if e = 2 then v2Arr else compA 315 v1Arr v2Arr))
        (conjA 315 cConj[1]! (if f = 0 then idA 315 else if f = 1 then v1Arr else
          if f = 2 then v2Arr else compA 315 v1Arr v2Arr))))

@[expose] def chkSP3 : Bool :=
  allLt cP3.pts.size fun m => [0, 1, 2].any fun k => (gensS 0).all fun s =>
    inCert (cS k) (conjInvA 315 cP3.pts[m]! s)

@[expose] def chkSP3Onto : Bool :=
  [0, 1, 2].all fun k => (List.range cP3.pts.size).any fun m => (gensS 0).all fun s =>
    inCert (cS k) (conjInvA 315 cP3.pts[m]! s)

@[expose] def chkSU : Bool := (List.range 4).all fun j => inCert (cS 0) u34Gens[j]!

@[expose] def chkSLaw : Bool :=
  (List.range 4).all fun a => (List.range 4).all fun b => (List.range 4).all fun c =>
    (List.range 4).all fun a' => (List.range 4).all fun b' => (List.range 4).all fun c' =>
      eqA 315 (compA 315 (phiA a b c) (phiA a' b' c'))
        (phiA (a ^^^ a') (b ^^^ b') (c ^^^ c' ^^^ mulCode4 a' b))

@[expose] def chkS : Bool :=
  chkSConj && chkSPieces && chkSNorm && chkSVWits && chkSTrip && chkSDistinct && chkSCz &&
    chkSProd && chkSP3 && chkSP3Onto && chkSU && chkSLaw

@[expose] def chkE0N : Bool :=
  allLt cNZ.pts.size fun k => !(inE 0 (conjA 315 cNZ.pts[k]! zArr) &&
    inE 0 (conjA 315 cNZ.pts[k]! xArr)) || inCert cNE cNZ.pts[k]!

@[expose] def chkE0C : Bool :=
  allLt cCz.pts.size fun k => !(commA cCz.pts[k]! xArr) || inE 0 cCz.pts[k]!

@[expose] def chkE0 : Bool := chkE0N && chkE0C

@[expose] def chkVk : Bool :=
  (aElts.all fun f => validA 315 f) && allLt vWits.size (fun k => okA vWits[k]!) &&
    allLt tripWit.size (fun k => okA tripWit[k]!) &&
    ([0, 1, 2].all fun k =>
      [vkArr k 1, vkArr k 2, compA 315 (vkArr k 1) (vkArr k 2)].all fun e =>
        (aElts.any fun f => eqA 315 (conjA 315 f e) (vkArr k 1)) &&
          (aElts.any fun f => eqA 315 (conjA 315 f e) (vkArr k 2))) &&
    ((List.range 4).all fun a => (List.range 4).all fun b => (List.range 4).all fun c =>
      (List.range 4).all fun a' => (List.range 4).all fun b' => (List.range 4).all fun c' =>
        (a == a' && b == b' && c == c') || !(eqA 315 (phiA a b c) (phiA a' b' c')))

@[expose] def j2Check45 : Bool :=
  chkElts45 && chkEnum45 && chkCent45 && chkLocal45 && chkW && chkS && chkE0 && chkVk

end CFSG.RankThree.PartTwo.Sec4.Sporadic.J2
