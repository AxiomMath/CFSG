module

public import CFSG.Sporadic.Co2Schreier.Defs
public import CFSG.Monster.B.Mathieu.SylowCore

public section

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Co2Cert
  CFSG.Monster.B.Mathieu

@[expose] def wordArr (A : Array (Array ℕ)) (w : List ℤ) : Array ℕ :=
  wordA 2300 A (rawInvs 2300 A) w

@[expose] def extendArrs (A : Array (Array ℕ)) (ds : List (List ℤ)) : Array (Array ℕ) :=
  ds.foldl (fun acc w => acc.push (wordArr acc w)) A

@[expose] def aArrs : Array (Array ℕ) := co2OrigArrs

@[expose] def cInitArrs : Array (Array ℕ) := (localRec.cInitialWords.map (wordArr aArrs)).toArray

@[expose] def dArrs : Array (Array ℕ) := (localRec.dWords.map (wordArr aArrs)).toArray

@[expose] def dStarArrs : Array (Array ℕ) := extendArrs dArrs localRec.dStrongDerivations

@[expose] def rArrs : Array (Array ℕ) := (localRec.rWords.map (wordArr dStarArrs)).toArray

@[expose] def z0Arr : Array ℕ := wordArr cInitArrs localRec.cInitialCenterWord

@[expose] def tArr : Array ℕ := wordArr dArrs localRec.dCenterWord

@[expose] def zArr : Array ℕ := wordArr rArrs localRec.zRWord

@[expose] def wArr : Array ℕ := wordArr aArrs localRec.alignmentIntermediateWord

@[expose] def xArr : Array ℕ := compA 2300 (compA 2300 wArr z0Arr) (invCand 2300 wArr)

@[expose] def hArr : Array ℕ :=
  compA 2300 (powArr 2300 (compA 2300 xArr zArr) ((oddN2 - 1) / 2))
    (powArr 2300 (compA 2300 z0Arr xArr) ((oddN1 - 1) / 2))

@[expose] def cArrs : Array (Array ℕ) :=
  cInitArrs.map fun g => compA 2300 (compA 2300 hArr g) (invCand 2300 hArr)

@[expose] def cStarArrs : Array (Array ℕ) := extendArrs cArrs localRec.cStrongDerivations

@[expose] def qArrs : Array (Array ℕ) := (localRec.qWords.map (wordArr cStarArrs)).toArray

@[expose] def sArrs : Array (Array ℕ) :=
  qArrs ++ (localRec.sQuotientWords.map (wordArr cStarArrs)).toArray

@[expose] def allInv (A : Array (Array ℕ)) : Bool :=
  allLt A.size fun j => isInvA 2300 A[j]! (invCand 2300 A[j]!)

end CFSG.Sporadic.Co2Schreier
