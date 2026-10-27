
module

public import CFSG.Sporadic.Schreier.ONCheckLocalBase
public import CFSG.Sporadic.Schreier.ONGlue
public meta import CFSG.Sporadic.Schreier.ONCheckLocalBase
public meta import CFSG.Sporadic.Schreier.ONGlue
public meta import Certificates.Data.CFSGNative.ONSchreier.Tools
public import Certificates.Data.CFSGNative.ONSchreier.Tools

public section

namespace CFSG.ONSchreier

open CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native

@[expose] def zArr : Array Nat := wordArr Data.zWord

@[expose] def qArr : Array Nat := wordArr Data.centerGeneratorWord

@[expose] def tArr : Array Nat := wordArr Data.tWord

@[expose] def cArr : Array Nat := wordArr Data.pairConjugatorWord

@[expose] def TStrong : Array (Array Nat) :=
  extendStrong nPts (wordArrs Data.TWords) Data.TChain.strongWords

@[expose] def MStrong : Array (Array Nat) :=
  extendStrong nPts (wordArrs Data.MWords) Data.MChain.strongWords

@[expose] def LStrong : Array (Array Nat) :=
  extendStrong nPts (wordArrs Data.LWords) Data.LChain.strongWords

@[expose] def memIn (S : Array (Array Nat)) (base : Array Nat) (g : Array Nat) : Bool :=
  memPoint (cLevels nPts base (allSteps S (pinvs nPts S) base)) (allInvSteps S (pinvs nPts S) base)
    base g

@[expose] def bPos : Array Nat := blockPos nPts Data.quotientBlocks

@[expose] def bTab (g : Array Nat) : Array Nat := blockTab g Data.quotientBlocks bPos

@[expose] def rPos : Array Nat := posArr nPts Data.TPoints

@[expose] def rTab (g : Array Nat) : Array Nat := restrictTab g Data.TPoints rPos

@[expose] def dConj : Array (Array Nat) :=
  (wordArrs Data.intersectionWords).map fun d => pcomp nPts (pinvCand nPts cArr) (pcomp nPts d cArr)

@[expose] def qPowArr : Nat → Array Nat
  | 0 => pid nPts
  | k + 1 => pcomp nPts qArr (qPowArr k)

@[expose] def cqcArr (k : Nat) : Array Nat :=
  pcomp nPts cArr (pcomp nPts (qPowArr k) (pinvCand nPts cArr))

end CFSG.ONSchreier
