module

public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Data3
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Check3Cert
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheck
public import CFSG.RankThree.Native.PermEnumeration
public import CFSG.Monster.B.Mathieu.SylowCore
public import Certificates.Data.CFSGNative.Schreier.Enum3
public meta import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Data3
public meta import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheck
public meta import CFSG.RankThree.Native.PermEnumeration
public meta import CFSG.Monster.B.Mathieu.SylowCore
public meta import Certificates.Data.CFSGNative.Schreier.Enum3
public meta import Mathlib.GroupTheory.Schreier
public import Mathlib.GroupTheory.Schreier

public section

namespace CFSG.RankThree.PartTwo.Sec4.Sporadic.J2

open CFSG.ComponentClassification.J2Cover CFSG.Certificates.Native CFSG.Monster.B.Co2.Native
  CFSG.RankThree.Native CFSG.Monster.B.Mathieu

@[expose] def keyPts : List ℕ := [0, 4, 3]

@[expose] def okA (t : Array ℕ) : Bool := validA 315 t && inP t

@[expose] def inCert (c : CFSG.Monster.B.Fischer.ArrCert) (t : Array ℕ) : Bool :=
  c.pts.toList.any (eqA 315 t)

@[expose] def inZ (t : Array ℕ) : Bool :=
  eqA 315 t (idA 315) || eqA 315 t zArr || eqA 315 t (compA 315 zArr zArr)

@[expose] def mapsInto (t S T : Array ℕ) : Bool := S.all fun p => T.contains t[p]!

@[expose] def permutesSets (F : Array (Array ℕ)) (t : Array ℕ) : Bool :=
  F.all fun S => F.any fun T => mapsInto t S T

@[expose] def fixesSets (F : Array (Array ℕ)) (t : Array ℕ) : Bool :=
  F.all fun S => mapsInto t S S

@[expose] def actsBy (F : Array (Array ℕ)) (t : Array ℕ) (σ : List ℕ) : Bool :=
  (List.range F.size).all fun i => mapsInto t F[i]! F[σ.getD i 0]!

@[expose] def gensP3 : Array (Array ℕ) := #[xArr, yArr]

@[expose] def gensNZArr : Array (Array ℕ) := gensCzArr.push g0Arr

@[expose] def gensNP : Array (Array ℕ) := #[xArr, yArr, h8Arr]

@[expose] def cP3 : CFSG.Monster.B.Fischer.ArrCert := cP3Lit

@[expose] def cCz : CFSG.Monster.B.Fischer.ArrCert := cCzLit

@[expose] def cNZ : CFSG.Monster.B.Fischer.ArrCert := cNZLit

@[expose] def cNP : CFSG.Monster.B.Fischer.ArrCert := cNPLit

@[expose] def chkElts : Bool :=
  okA xArr && okA yArr && okA zArr && okA g0Arr && okA h8Arr &&
    allLt gensCzArr.size (fun k => okA gensCzArr[k]!) &&
    eqA 315 (powArr 315 xArr 3) (idA 315) && eqA 315 (powArr 315 yArr 3) (idA 315) &&
    eqA 315 zArr (commutatorA 315 xArr yArr) && commA zArr xArr &&
    commA zArr yArr &&
    !(eqA 315 zArr (idA 315)) &&
    allLt gensCzArr.size (fun k => commA gensCzArr[k]! zArr) &&
    eqA 315 (conjA 315 g0Arr zArr) (compA 315 zArr zArr) &&
    inCert cP3 (conjA 315 h8Arr xArr) && inCert cP3 (conjA 315 h8Arr yArr) &&
    !(inCert cP3 (powArr 315 h8Arr 4)) && inCert cP3 (powArr 315 h8Arr 8)

@[expose] def chkEnum : Bool :=
  enumOK 315 gensP3 keyPts cP3 && cP3.pts.size == 27 &&
    enumOK 315 gensCzArr keyPts cCz && cCz.pts.size == 1080 &&
    enumOK 315 gensNZArr keyPts cNZ && cNZ.pts.size == 2160 &&
    enumOK 315 gensNP keyPts cNP && cNP.pts.size == 216

@[expose] def zConj (k : ℕ) (t : Array ℕ) : Array ℕ := conjA 315 autStrong[k]! t

@[expose] def cZo : CFSG.Monster.B.Fischer.ArrCert := cZoLit

@[expose] def chkClass : Bool :=
  validA 315 autStrong[0]! && validA 315 autStrong[1]! &&
    CFSG.Monster.B.Fischer.arrCertOK zConj 2 okA (keyA 315 keyPts) zArr cZo &&
    cZo.pts.size == 560

@[expose] def chkNP : Bool :=
  allLt cNZ.pts.size fun k =>
    let t := cNZ.pts[k]!
    !(inCert cP3 (conjA 315 t xArr) && inCert cP3 (conjA 315 t yArr)) || inCert cNP t

@[expose] def chkFix : Bool :=
  CFSG.ComponentClassification.J2Cover.fixedCount 315 zArr == 45 &&
    allLt cP3.pts.size fun k =>
      inZ cP3.pts[k]! || CFSG.ComponentClassification.J2Cover.fixedCount 315 cP3.pts[k]! == 0

@[expose] def chkSix : Bool :=
  (allLt cCz.pts.size fun k =>
      permutesSets o6Sets cCz.pts[k]! && (!(fixesSets o6Sets cCz.pts[k]!) || inZ cCz.pts[k]!)) &&
    (allLt gensCzArr.size fun k => actsBy o6Sets gensCzArr[k]! (sigCz.getD k []))

@[expose] def chkTen : Bool :=
  (allLt cNZ.pts.size fun k =>
      permutesSets s10Sets cNZ.pts[k]! &&
        (!(fixesSets s10Sets cNZ.pts[k]!) || inZ cNZ.pts[k]!)) &&
    (allLt gensNZArr.size fun k => actsBy s10Sets gensNZArr[k]! (sigNZ.getD k []))

@[expose] def setsOK (F : Array (Array ℕ)) (m : ℕ) : Bool :=
  (F.all fun S => S.size == m && S.all (fun p => decide (p < 315)) && decide S.toList.Nodup) &&
    (List.range F.size).all fun i => (List.range F.size).all fun j =>
      i == j || F[i]!.any fun p => !(F[j]!.contains p)

@[expose] def chkSets : Bool :=
  o6Sets.size == 6 && setsOK o6Sets 15 && fixesSets o6Sets zArr &&
    s10Sets.size == 10 && setsOK s10Sets 9 && fixesSets s10Sets zArr

@[expose] def bArr (j : ℕ) : Array ℕ :=
  if j = 0 then xArr else if j = 1 then yArr else if j = 2 then compA 315 xArr yArr
  else compA 315 xArr (compA 315 yArr yArr)

@[expose] def inE (j : ℕ) (t : Array ℕ) : Bool :=
  (List.range 3).any fun a => (List.range 3).any fun c =>
    eqA 315 t (compA 315 (powArr 315 zArr a) (powArr 315 (bArr j) c))

@[expose] def chkDelta : Bool :=
  [1, 2, 3].all fun j => (List.range cNP.pts.size).any fun k =>
    inE j (conjInvA 315 cNP.pts[k]! zArr) && inE j (conjInvA 315 cNP.pts[k]! xArr)

@[expose] def j2Check3 : Bool :=
  chkElts && chkEnum && chkClass && chkNP && chkFix && chkSix && chkTen && chkSets && chkDelta

end CFSG.RankThree.PartTwo.Sec4.Sporadic.J2
