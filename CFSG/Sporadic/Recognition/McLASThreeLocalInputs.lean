module

public import CFSG.Sporadic.Recognition.McLASInputs
public import CFSG.Sporadic.Recognition.McLASThreeLocalData
public meta import CFSG.Sporadic.Recognition.McLASInputs
public meta import CFSG.Sporadic.Recognition.McLASThreeLocalData
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

@[expose] def invHTab : Table := tlTbl 0

@[expose] def outerOTab : Table := tlTbl 1

@[expose] def rGens3 : Array Table := ((List.range 5).map fun i => tlTbl (i + 2)).toArray

@[expose] def aGens3 : Array Table := ((List.range 4).map fun i => tlTbl (i + 7)).toArray

@[expose] def sigmaTab : Table := tlTbl 14

@[expose] def conjGTab : Table := tlTbl 11

@[expose] def commATab : Table := tlTbl 12

@[expose] def commBTab : Table := tlTbl 13

@[expose] def cpGens3 : Array Table := #[threeTbl 0, threeTbl 1, threeTbl 2]

@[expose] def gxGens : Array Table := cpGens3.push invHTab

@[expose] def subEnumOK (n cap order : Nat) (sift : Table → Bool) (sg : Array Table) : Bool :=
  let E := mulClosureH n sg cap
  sg.all (fun g => permOK n g && sift g && invOK n g (invT n g)) &&
    mulTreeOK n sg E.1 E.2.1 E.2.2 && closedOK n (sg ++ sg.map (invT n)) E.1 &&
    hkeysDistinct n E.1.toList && E.1.size == order

@[expose] def enumT : Array Table × Array Nat × Array Nat :=
  mulClosureH 275 sylowThreeGens.toArray 800

@[expose] def enumR3 : Array Table × Array Nat × Array Nat := mulClosureH 275 rGens3 300

@[expose] def enumA3 : Array Table × Array Nat × Array Nat := mulClosureH 275 aGens3 200

@[expose] def enumClass : Closure :=
  conjClosureH 275 mclPGTbls mclPGInvTbls (threeTbl 0) 30800

@[expose] def threeEnumCheck : Bool :=
  subEnumOK 275 800 729 mclSift sylowThreeGens.toArray && subEnumOK 275 300 243 mclSift rGens3 &&
  subEnumOK 275 200 81 mclSift aGens3 &&
  allIn 0 mclPGTbls.size (fun l => invOK 275 mclPGTbls[l]! mclPGInvTbls[l]!) &&
  permOK 275 (threeTbl 0) && invOK 275 (threeTbl 0) (invT 275 (threeTbl 0)) &&
  conjTreeOK 275 mclPGTbls mclPGInvTbls (threeTbl 0) enumClass.1 enumClass.2.1 enumClass.2.2 &&
  hkeysDistinct 275 enumClass.1.toList && enumClass.1.size == 30800

@[expose] def gxCheck : Bool :=
  permOK 275 (threeTbl 0) && invOK 275 (threeTbl 0) (invT 275 (threeTbl 0)) &&
  permOK 275 mclOuterTbl && permOK 275 invHTab && invOK 275 invHTab (invT 275 invHTab) &&
  mclSift invHTab &&
  tblEq 275 (conjT 275 invHTab (invT 275 invHTab) (threeTbl 0)) (invT 275 (threeTbl 0)) &&
  permOK 275 outerOTab && invOK 275 outerOTab (invT 275 outerOTab) &&
  commTT 275 outerOTab (threeTbl 0) && !mclSift outerOTab &&
  mclSift (compT 275 outerOTab mclOuterTbl)

@[expose] def rInTCheck : Bool :=
  enumR3.1.all (memT 275 enumT.1) && enumA3.1.all (memT 275 enumT.1) &&
  rGens3.all (commTT 275 (threeTbl 0)) && sylowThreeGens.all (commTT 275 (threeTbl 0))

@[expose] def rNormalCheck : Bool :=
  gxGens.all (fun c => permOK 275 c && invOK 275 c (invT 275 c)) &&
  gxGens.all fun c => rGens3.all fun r => memT 275 enumR3.1 (conjT 275 c (invT 275 c) r)

@[expose] def sylowIntCheck : Bool :=
  permOK 275 conjGTab && invOK 275 conjGTab (invT 275 conjGTab) && mclSift conjGTab &&
  (tblEq 275 (conjT 275 conjGTab (invT 275 conjGTab) (threeTbl 0)) (threeTbl 0) ||
    tblEq 275 (conjT 275 conjGTab (invT 275 conjGTab) (threeTbl 0)) (invT 275 (threeTbl 0))) &&
  enumT.1.all fun e => !memT 275 enumT.1 (conjT 275 (invT 275 conjGTab) conjGTab e) ||
    memT 275 enumR3.1 e

@[expose] def rStructCheck : Bool :=
  enumR3.1.all (fun r => invOK 275 r (invT 275 r)) &&
  enumR3.1.all (fun e => tblEq 275 (powT 275 3 e) (idT 275)) &&
  (enumR3.1.toList.filter fun e => rGens3.all (commTT 275 e)).length == 3 &&
  memT 275 enumR3.1 (threeTbl 0) &&
  enumR3.1.all (fun a => enumR3.1.all fun b =>
    let c := compT 275 (compT 275 a b) (compT 275 (invT 275 a) (invT 275 b))
    tblEq 275 c (idT 275) || tblEq 275 c (threeTbl 0) || tblEq 275 c (invT 275 (threeTbl 0))) &&
  permOK 275 commATab && permOK 275 commBTab && memT 275 enumR3.1 commATab &&
  memT 275 enumR3.1 commBTab && invOK 275 commATab (invT 275 commATab) &&
  invOK 275 commBTab (invT 275 commBTab) &&
  tblEq 275 (compT 275 (compT 275 commATab commBTab)
    (compT 275 (invT 275 commATab) (invT 275 commBTab))) (threeTbl 0)

@[expose] def aStructCheck : Bool :=
  enumR3.1.all (fun r => invOK 275 r (invT 275 r)) &&
  enumA3.1.all (fun a => enumA3.1.all fun b => commTT 275 a b) &&
  enumA3.1.all (fun e => tblEq 275 (powT 275 3 e) (idT 275)) &&
  (enumA3.1.toList.filter (memT 275 enumR3.1)).length == 27 &&
  enumT.1.all (fun e => enumR3.1.any fun r => memT 275 enumA3.1 (compT 275 (invT 275 r) e)) &&
  enumT.1.all (fun e => !ordTest 275 3 e || memT 275 enumR3.1 e || memT 275 enumA3.1 e) &&
  aGens3.all (fun g => memT 275 enumClass.1 g) &&
  enumT.1.all (fun e => !memT 275 enumClass.1 e || memT 275 enumA3.1 e) &&
  (enumT.1.toList.filter (memT 275 enumClass.1)).length == 20

@[expose] def aInvCheck : Bool :=
  permOK 275 sigmaTab && invOK 275 sigmaTab (invT 275 sigmaTab) && permOK 275 mclOuterTbl &&
  !mclSift sigmaTab && mclSift (compT 275 sigmaTab mclOuterTbl) &&
  tblEq 275 (compT 275 sigmaTab sigmaTab) (idT 275) &&
  aGens3.all fun a => tblEq 275 (conjT 275 sigmaTab (invT 275 sigmaTab) a) (invT 275 a)

@[expose] def weakCheck : Bool :=
  enumR3.1.all fun r => !memT 275 enumClass.1 r || tblEq 275 r (threeTbl 0) ||
    tblEq 275 r (invT 275 (threeTbl 0))

@[expose] def thompsonCheck : Bool :=
  enumT.1.all (fun t => memT 275 enumA3.1 t ||
    Nat.ble (enumA3.1.toList.filter (commTT 275 t)).length 9) &&
  (enumT.1.toList.filter fun e => sylowThreeGens.toArray.all (commTT 275 e)).length == 3

@[expose] def threeLocalCheck : Bool :=
  threeEnumCheck && gxCheck && rInTCheck && rNormalCheck && sylowIntCheck && rStructCheck &&
    aStructCheck && aInvCheck && weakCheck && thompsonCheck

end CFSG.Sporadic.Recognition.McLAS
