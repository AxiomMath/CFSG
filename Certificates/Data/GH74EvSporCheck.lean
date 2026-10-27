module

public import CFSG.Sporadic.SmallOddCore.J2CheckInputs
public import CFSG.Sporadic.SmallOddCore.CentData
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutNative
public import Certificates.Data.GH74EvSporData
public import Certificates.Data.CFSGNative.SporadicSchreier.Count
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizerData
public meta import CFSG.Sporadic.SmallOddCore.J2CheckInputs
public meta import CFSG.Sporadic.SmallOddCore.CentData
public meta import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutNative
public meta import Certificates.Data.GH74EvSporData
public meta import Certificates.Data.CFSGNative.SporadicSchreier.Count
public meta import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizerData
public meta import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutFusion
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutFusion

public section

namespace CFSG.GH74.Generic.S45.EvSpor

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native CFSG.ComponentClassification.J2Cover
open CFSG.Sporadic.Schreier (blockHom m12A1 m12Sigma toTable)
open CFSG.ComponentClassification.M12Cover (permZ q4Gens)

@[expose] def cap : Nat := 3000

@[expose] def closArr (n cap : Nat) (gs : List Table) : Array Table := (mulClosureH n gs.toArray cap).1

@[expose] def enumOK (n cap : Nat) (gs : List Table) (sz : Nat) : Bool :=
  gs.all (fun g => permOK n g && invOK n g (invT n g)) &&
    mulTreeOK n gs.toArray (mulClosureH n gs.toArray cap).1 (mulClosureH n gs.toArray cap).2.1
      (mulClosureH n gs.toArray cap).2.2 &&
    closedOK n (gs.toArray ++ gs.toArray.map (invT n)) (mulClosureH n gs.toArray cap).1 &&
    hkeysDistinct n (mulClosureH n gs.toArray cap).1.toList &&
    (mulClosureH n gs.toArray cap).1.size == sz

@[expose] def invsOK (n : Nat) (E : Array Table) : Bool := E.all fun x => invOK n x (invT n x)

@[expose] def cent5OK (n : Nat) (C : Array Table) (t v : Table) : Bool :=
  C.all fun z => !ordTest n 5 z ||
    ((C.all fun c => !commTT n c z || (List.range 5).any fun j =>
        tblEq n c (powT n j z) || tblEq n c (compT n t (powT n j z))) &&
      C.all fun c => !commTT n (compT n v c) z)

@[expose] def outerCommOK (n : Nat) (sift : Table → Bool) (u t v : Table) : Bool :=
  permOK n v && involOK n v && !sift v && sift (compT n v u) && commTT n v t

@[expose] def derivedInOK (n : Nat) (D M : Array Table) : Bool :=
  D.all fun x => D.all fun y =>
    memT n M (compT n (compT n x y) (compT n (invT n x) (invT n y)))

@[expose] def innerDerivedOK (n : Nat) (inner : Table → Bool) (D M : Array Table) : Bool :=
  D.all fun x => !inner x || D.all fun y => !inner y ||
    memT n M (compT n (compT n x y) (compT n (invT n x) (invT n y)))

@[expose] def elemAbOK (n : Nat) (E : Array Table) : Bool :=
  E.all fun x => tblEq n (compT n x x) (idT n) && E.all fun y => commTT n x y

@[expose] def conjInOK (n : Nat) (M : Array Table) (a b e : Table) : Bool :=
  memT n M (conjT n e (invT n e) a) && memT n M (conjT n e (invT n e) b)

@[expose] def normPred (n : Nat) (M : Array Table) (a b : Table) (g : Table) : Bool :=
  conjInOK n M a b g

@[expose] def normCount (n : Nat) (Tss : List (List Table)) (M : Array Table) (a b : Table) : Nat :=
  countProducts n (normPred n M a b) Tss (idT n)

@[expose] def j2Row2A : ClassRow := j2Rows[2]'(by decide)

@[expose] def j2Row2B : ClassRow := j2Rows[1]'(by decide)

@[expose] def j2C2A : Array Table := closArr 315 cap j2Row2A.centGens

@[expose] def j2C2B : Array Table := closArr 315 cap j2Row2B.centGens

@[expose] def j2KbGens : List Table := [j2KbA, j2KbB]

@[expose] def j2Kb : Array Table := closArr 315 cap j2KbGens

@[expose] def j2E16Gens : List Table := [j2E0, j2E1, j2E2, j2E3]

@[expose] def j2E16 : Array Table := closArr 315 cap j2E16Gens

@[expose] def j2RepsOK : Bool :=
  permOK 315 j2OuterTbl && permOK 315 j2Row2A.rep && permOK 315 j2Row2B.rep

@[expose] def j2C2AEnumOK : Bool := enumOK 315 cap j2Row2A.centGens 1920 && invsOK 315 j2C2A

@[expose] def j2C2BEnumOK : Bool := enumOK 315 cap j2Row2B.centGens 240 && invsOK 315 j2C2B

@[expose] def j2Cent5OK : Bool := cent5OK 315 j2C2A j2Row2A.rep j2VA

@[expose] def j2OuterOK : Bool :=
  outerCommOK 315 j2Sift j2OuterTbl j2Row2A.rep j2VA &&
    outerCommOK 315 j2Sift j2OuterTbl j2Row2B.rep j2VB

@[expose] def j2KbEnumOK : Bool :=
  enumOK 315 cap j2KbGens 60 && j2KbGens.all j2Sift

@[expose] def j2DerivedOK : Bool := derivedInOK 315 j2C2B j2Kb

@[expose] def j2NormCount : Nat :=
  normCount 315 (chainTables 315 CFSG.Sporadic.Schreier.PairNative.j2StrongArrs
    CFSG.Sporadic.Schreier.PairJ2.baseArr) j2Kb j2KbA j2KbB

@[expose] def j2E16OK : Bool :=
  enumOK 315 cap j2E16Gens 16 && j2E16Gens.all j2Sift && elemAbOK 315 j2E16 &&
    j2E16Gens.all (conjInOK 315 j2Kb j2KbA j2KbB)

@[expose] def m12ZT : Table := toTable (blockHom (permZ, permZ))

@[expose] def m12AT : Table := toTable m12A1

@[expose] def m12ST : Table := toTable m12Sigma

@[expose] def m12CGens : List Table := q4Gens.map toTable

@[expose] def m12C2A : Array Table := closArr 24 cap m12CGens

@[expose] def m12KaGens : List Table := [m12AT, m12KaB]

@[expose] def m12Ka : Array Table := closArr 24 cap m12KaGens

@[expose] def innerT (x : Table) : Bool := (x[0]!).toNat < 12

@[expose] def m12RepsOK : Bool :=
  permOK 24 m12ZT && involOK 24 m12ZT && permOK 24 m12AT && involOK 24 m12AT && permOK 24 m12ST &&
    involOK 24 m12ST

@[expose] def m12C2AEnumOK : Bool := enumOK 24 cap m12CGens 480 && invsOK 24 m12C2A

@[expose] def m12KaEnumOK : Bool :=
  enumOK 24 cap m12KaGens 60 && memT 24 m12C2A m12AT && memT 24 m12C2A m12KaB

@[expose] def m12DerivedOK : Bool := innerDerivedOK 24 innerT m12C2A m12Ka

@[expose] def m12OuterOK : Bool :=
  commTT 24 m12ST m12ZT && commTT 24 m12ST m12AT && commTT 24 m12ST m12KaB

end CFSG.GH74.Generic.S45.EvSpor
