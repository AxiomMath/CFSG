module

public import CFSG.RankThree.Native.HSMcLFiveData
public import CFSG.RankThree.Native.HSMcLFiveAux
public import CFSG.RankThree.Native.HSMcLSmallCheck
public import CFSG.RankThree.Native.FiveKit
public import CFSG.Sporadic.Schreier.PairMcLCheck
public meta import CFSG.RankThree.Native.HSMcLFiveData
public meta import CFSG.RankThree.Native.HSMcLFiveAux
public meta import CFSG.RankThree.Native.HSMcLSmallCheck
public meta import CFSG.RankThree.Native.HSMcLSmallData
public meta import CFSG.RankThree.Native.HSMcLAuxData
public meta import CFSG.RankThree.Native.FiveKit
public meta import CFSG.RankThree.Native.ChainCentralizer
public meta import CFSG.RankThree.Native.PermEnumeration
public meta import CFSG.Sporadic.Schreier.PairMcLCheck
public meta import CFSG.Sporadic.Schreier.PairMcLCert
public meta import CFSG.Sporadic.SmallOddCore.McLData
public meta import CFSG.Monster.B.Fischer.InducedData
public meta import CFSG.Monster.B.Mathieu.SylowCore
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.SmallOddCore.Check

public noncomputable section

namespace CFSG.RankThree.Native

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Mathieu
  CFSG.Monster.B.Fischer CFSG.Sporadic.Schreier

@[expose] def caseChainOK (n : ℕ) (S : Array (Array ℕ)) (base : Array ℕ) (W : Array (List ℤ))
    (a b u : Array ℕ) : Bool :=
  rawChainOK n (S.extract 0 3) S base W 1 && eqA n S[0]! a && eqA n S[1]! b && eqA n S[2]! u

@[expose] def centOK (n : ℕ) (S : Array (Array ℕ)) (base x : Array ℕ)
    (rels : List (ℕ × ℕ × ℕ)) (gs : Array (Array ℕ)) (ps : List ℕ) (c : ArrCert) (N : ℕ) : Bool :=
  relsOK n base x rels && enumOK n gs ps c && c.pts.size == N &&
    allLt gs.size (fun k => commA n gs[k]! x) &&
    allLt gs.size (fun k => siftA n (rawLevels n S base) base 0 gs[k]!) &&
    ptailOK n (rawLevels n S base) base x (pow5A n x) rels c.pts.toList base.size 0 (idA n)

@[expose] def normalOK (n : ℕ) (gC gA : Array (Array ℕ)) (ps : List ℕ) (cC cA : ArrCert) (N : ℕ)
    (PL : Array Level) (Pb : Array ℕ) : Bool :=
  enumOK n gA ps cA && cA.pts.size == N &&
    allLt cA.pts.size (fun k => eqA n (powArr n cA.pts[k]! 5) (idA n)) &&
    allLt gA.size (fun l => cC.pts.toList.any (eqA n gA[l]!)) &&
    allLt gC.size (fun k => allLt gA.size fun l =>
      cA.pts.toList.any (eqA n (conjA n gC[k]! gA[l]!))) &&
    allLt gA.size (fun l => siftA n PL Pb 0 gA[l]!)

@[expose] def selfCentOK (n : ℕ) (gA : Array (Array ℕ)) (cC cA : ArrCert) : Bool :=
  allLt gA.size (fun l => allLt gA.size fun l' => commA n gA[l]! gA[l']!) &&
    allLt cC.pts.size (fun k => !(allLt gA.size fun l => commA n cC.pts[k]! gA[l]!) ||
      cA.pts.toList.any (eqA n cC.pts[k]!))

@[expose] def zCentOK (n : ℕ) (gA : Array (Array ℕ)) (cC cA : ArrCert) (x : Array ℕ) : Bool :=
  cA.pts.toList.any (eqA n x) &&
    allLt cC.pts.size (fun k => !(allLt gA.size fun l => commA n cC.pts[k]! gA[l]!) ||
      (List.range 5).any fun e => eqA n cC.pts[k]! (powArr n x e))

@[expose] def derivedOK (n : ℕ) (gC gD : Array (Array ℕ)) (ps : List ℕ) (cC cD : ArrCert)
    (c d x : Array ℕ) (PL : Array Level) (Pb : Array ℕ) : Bool :=
  enumOK n gD ps cD && cD.pts.size == 60 && validA n c && validA n d &&
    cC.pts.toList.any (eqA n c) && cC.pts.toList.any (eqA n d) &&
    eqA n gC[2]! (commutatorA n c d) &&
    allLt gC.size (fun k => allLt gD.size fun l =>
      cD.pts.toList.any (eqA n (conjA n gC[k]! gD[l]!))) &&
    allLt gC.size (fun k => allLt gC.size fun l =>
      cD.pts.toList.any (eqA n (commutatorA n gC[k]! gC[l]!))) &&
    !(commA n gD[0]! gD[1]!) && conjSimpleOK n ps cD &&
    allLt cC.pts.size (fun k => !(allLt gD.size fun l => commA n cC.pts[k]! gD[l]!) ||
      (List.range 5).any fun e => eqA n cC.pts[k]! (powArr n x e)) &&
    allLt gD.size (fun l => siftA n PL Pb 0 gD[l]!)

@[expose] def transOK (n : ℕ) (H L : Array (Array ℕ)) (rec : List ℕ) (RL : Array Level)
    (Rb : Array ℕ) : Bool :=
  allLt 31 fun j => validA n H[j]! && siftA n RL Rb 0 H[j]! &&
    eqA n (conjA n H[j]! L[rec.getD j 0 % 31]!) L[j]!

@[expose] def hs100FiveKeys : List ℕ := hs100RBase.map Fin.val

@[expose] def hs100PLevels : Array Level := rawLevels 100 hs100StrongArrs hs100BaseArr

@[expose] def hs100RLevels : Array Level := rawLevels 100 hs100RArrs hs100RBaseArr

@[expose] def hs100Case0BaseArr : Array ℕ := (hs100Case0Base.map Fin.val).toArray

@[expose] def hs100Case2BaseArr : Array ℕ := (hs100Case2Base.map Fin.val).toArray

@[expose] def hs100Case23BaseArr : Array ℕ := (hs100Case23Base.map Fin.val).toArray

@[expose] def hs100FiveDGens : Array (Array ℕ) :=
  #[commutatorA 100 hs100FiveC2Gens[1]! hs100FiveC2Gens[2]!, hs100FiveC2Gens[2]!]

@[expose] def hs100FiveQCert : ArrCert := enumBfs 100 hs100FiveQGens hs100FiveKeys 130

@[expose] def hs100FiveC0Cert : ArrCert := enumBfs 100 hs100FiveC0Gens hs100FiveKeys 60

@[expose] def hs100FiveC2Cert : ArrCert := enumBfs 100 hs100FiveC2Gens hs100FiveKeys 620

@[expose] def hs100FiveC23Cert : ArrCert := enumBfs 100 hs100FiveC23Gens hs100FiveKeys 1020

@[expose] def hs100FiveA0Cert : ArrCert := enumBfs 100 hs100FiveA0Gens hs100FiveKeys 30

@[expose] def hs100FiveA23Cert : ArrCert := enumBfs 100 hs100FiveA23Gens hs100FiveKeys 130

@[expose] def hs100FiveDCert : ArrCert := enumBfs 100 hs100FiveDGens hs100FiveKeys 70

@[expose] def mcl275FiveKeys : List ℕ := mcl275RBase.map Fin.val

@[expose] def mcl275PLevels : Array Level := rawLevels 275 mclStrongArrs PairMcL.baseArr

@[expose] def mcl275RLevels : Array Level := rawLevels 275 mcl275RArrs mcl275RBaseArr

@[expose] def mcl275Case0BaseArr : Array ℕ := (mcl275Case0Base.map Fin.val).toArray

@[expose] def mcl275Case1BaseArr : Array ℕ := (mcl275Case1Base.map Fin.val).toArray

@[expose] def mcl275FiveQCert : ArrCert := enumBfs 275 mcl275FiveQGens mcl275FiveKeys 130

@[expose] def mcl275FiveC0Cert : ArrCert := enumBfs 275 mcl275FiveC0Gens mcl275FiveKeys 60

@[expose] def mcl275FiveC1Cert : ArrCert := enumBfs 275 mcl275FiveC1Gens mcl275FiveKeys 1600

@[expose] def mcl275FiveA0Cert : ArrCert := enumBfs 275 mcl275FiveA0Gens mcl275FiveKeys 30

@[expose] def mcl275FiveA1Cert : ArrCert := enumBfs 275 mcl275FiveA1Gens mcl275FiveKeys 130

end CFSG.RankThree.Native
