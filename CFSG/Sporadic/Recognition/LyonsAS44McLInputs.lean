module

public import CFSG.Sporadic.Recognition.LyonsAS44McLData
public import CFSG.Sporadic.Recognition.McLASThreeLocalInputs
public meta import CFSG.Sporadic.Recognition.LyonsAS44McLData
public meta import CFSG.Sporadic.Recognition.McLASThreeLocalInputs
public meta import CFSG.Sporadic.Recognition.McLASThreeLocalData
public meta import CFSG.Sporadic.Recognition.McLASInputs
public meta import CFSG.Sporadic.SmallOddCore.McLCheckInputs
public meta import CFSG.Sporadic.SmallOddCore.McLData
public meta import CFSG.Sporadic.SmallOddCore.CentData
public meta import Certificates.Data.CFSGNative.SmallOddCore.Check
public meta import Certificates.Data.CFSGNative.SporadicSchreier.Count

public section

namespace CFSG.Sporadic.Recognition.McLAS

open CFSG.PSL3Four.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.Sporadic.SuzOddCore CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.Schreier

@[expose] def nrmY : Array Table := (List.range 10).toArray.map nrmTbl

@[expose] def nrmN : Array Table := #[nrmTbl 10, nrmTbl 11]

@[expose] def nrmC : Array Table := (List.range 10).toArray.map fun i => nrmTbl (12 + i)

@[expose] def nrmPt (z : Table) : Nat :=
  ((List.range 10).find? fun j =>
    tblEq 275 z nrmY[j]! || tblEq 275 z (invT 275 nrmY[j]!)).getD 10

@[expose] def nrmAct (n : Table) : Table :=
  Array.ofFn (n := 10) fun i => UInt32.ofNat (nrmPt (conjT 275 n (invT 275 n) nrmY[i.val]!))

@[expose] def nrmW : Array Table := nrmN.map nrmAct

@[expose] def nrmClosure : Array Table × Array Nat × Array Nat := mulClosureH 10 nrmW 800

@[expose] def nrmYCheck : Bool :=
  nrmY.size == 10 && tblEq 275 nrmY[0]! (threeTbl 0) &&
  nrmY.all (fun y => permOK 275 y && invOK 275 y (invT 275 y) && memT 275 enumA3.1 y &&
    memT 275 enumClass.1 y) &&
  (List.range 10).all (fun i => (List.range 10).all fun j =>
    i == j || (!tblEq 275 nrmY[i]! nrmY[j]! && !tblEq 275 nrmY[i]! (invT 275 nrmY[j]!))) &&
  enumA3.1.all fun z => !memT 275 enumClass.1 z ||
    nrmY.any fun y => tblEq 275 z y || tblEq 275 z (invT 275 y)

@[expose] def nrmNormCheck : Bool :=
  nrmN.size == 2 &&
  nrmN.all (fun n => permOK 275 n && mclSift n && invOK 275 n (invT 275 n) &&
    aGens3.all fun a => memT 275 enumA3.1 (conjT 275 n (invT 275 n) a)) &&
  nrmN.all fun n => nrmY.all fun y => nrmPt (conjT 275 n (invT 275 n) y) < 10

@[expose] def nrmTransCheck : Bool :=
  nrmW.all (permOK 10) &&
  mulTreeOK 10 nrmW nrmClosure.1 nrmClosure.2.1 nrmClosure.2.2 &&
  (List.range 10).all fun a => (List.range 10).all fun b => (List.range 10).all fun c =>
    a == b || a == c || b == c ||
      nrmClosure.1.any fun e => ap e 0 == a && ap e 1 == b && ap e 2 == c

@[expose] def nrmConjCheck : Bool :=
  nrmC.size == 10 &&
  nrmC.all (fun c => permOK 275 c && mclSift c && invOK 275 c (invT 275 c) &&
    commTT 275 c (threeTbl 0)) &&
  (List.range 10).all fun i => (List.range 10).all fun j =>
    i == j || aGens3.any fun a => !memT 275 enumA3.1
      (conjT 275 (invT 275 nrmC[j]!) nrmC[j]! (conjT 275 nrmC[i]! (invT 275 nrmC[i]!) a))

@[expose] def nrmCheck : Bool := nrmYCheck && nrmNormCheck && nrmTransCheck && nrmConjCheck

end CFSG.Sporadic.Recognition.McLAS
