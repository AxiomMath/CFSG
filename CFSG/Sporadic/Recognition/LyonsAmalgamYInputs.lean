module

public import CFSG.Sporadic.Recognition.LyonsAmalgamYData
public import CFSG.Sporadic.SmallOddCore.LocalCheck
public meta import CFSG.Sporadic.Recognition.LyonsAmalgamYData
public meta import CFSG.Sporadic.SmallOddCore.LocalCheck

public section

namespace CFSG.Sporadic.Recognition.LyonsSims.Ly1080

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native

abbrev deg : Nat := 1080

@[expose] def uTabs : Array Table := Array.ofFn (n := 4) fun i => hexT 3 deg (deg * i.val) uHex

@[expose] def uInvTabs : Array Table := uTabs.map (invT deg)

@[expose] def sigmaTab : Table := hexT 3 deg 0 sigmaHex

@[expose] def uLet (l : Int) : Table :=
  if 0 < l then uTabs[l.toNat - 1]! else uInvTabs[(-l).toNat - 1]!

@[expose] def abLet (l : Int) : Table :=
  if l = 1 then uTabs[0]! else if l = 2 then uTabs[3]! else
    if l = -1 then uInvTabs[0]! else uInvTabs[3]!

@[expose] def txyTabs : Array Table := txyWords.toArray.map (wordT deg uLet)

@[expose] def txyInvTabs : Array Table := txyTabs.map (invT deg)

@[expose] def txyLet (l : Int) : Table :=
  if 0 < l then txyTabs[l.toNat - 1]! else txyInvTabs[(-l).toNat - 1]!

@[expose] def wordsOK : Bool :=
  (erelWords ++ txyWords).all (fun w => w.all fun l => l != 0 && l.natAbs ≤ 4) &&
    (genWords ++ autRelators ++ autWitnesses).all
      (fun w => w.all fun l => l != 0 && l.natAbs ≤ 2) &&
    sigmaTxyWords.all (fun w => w.all fun l => l != 0 && l.natAbs ≤ 5)

@[expose] def tablesOK : Bool :=
  uTabs.size == 4 && txyTabs.size == 5 && wordsOK &&
    (uTabs.toList ++ [sigmaTab] ++ txyTabs.toList).all (fun T => permOK deg T &&
      invOK deg T (invT deg T)) &&
    tblEq deg (compT deg sigmaTab sigmaTab) (idT deg)

@[expose] def erelOK : Bool :=
  erelWords.length == 4 &&
    (List.range 4).all fun i =>
      tblEq deg (conjT deg sigmaTab sigmaTab uTabs[i]!) (wordT deg uLet erelWords[i]!)

@[expose] def genOK : Bool :=
  genWords.length == 2 && tblEq deg uTabs[1]! (wordT deg abLet genWords[0]!) &&
    tblEq deg uTabs[2]! (wordT deg abLet genWords[1]!)

@[expose] def abTabs : Array Table := #[uTabs[0]!, uTabs[3]!]

@[expose] def enumCap : Nat := 400000

@[expose] def enumY : Array Table × Array Nat × Array Nat := mulClosureH deg abTabs enumCap

@[expose] def yEnumOK : Bool :=
  mulTreeOK deg abTabs enumY.1 enumY.2.1 enumY.2.2 && hkeysDistinct deg enumY.1.toList &&
    enumY.1.size == 349920

@[expose] def yCenterOK : Bool :=
  enumY.1.all fun x => !(commTT deg x abTabs[0]! && commTT deg x abTabs[1]!) ||
    tblEq deg x (idT deg)

@[expose] def txyCap : Nat := 5000

@[expose] def txyEnum : Array Table × Array Nat × Array Nat :=
  mulClosureH deg txyTabs.toList.toArray txyCap

@[expose] def txyEnumOK : Bool := CFSG.Sporadic.SmallOddCore.enumOK deg txyCap 3888 txyTabs.toList

@[expose] def normSweepOK : Bool :=
  enumY.1.all fun x =>
    let xi := invT deg x
    invOK deg x xi &&
      (!(txyTabs.all fun t => memT deg txyEnum.1 (conjT deg x xi t)) || memT deg txyEnum.1 x)

@[expose] def outerOK : Bool :=
  txyEnum.1.all fun t =>
    let ti := invT deg t
    invOK deg t ti &&
      !((List.range 4).all fun i =>
        tblEq deg (conjT deg t ti uTabs[i]!) (conjT deg sigmaTab sigmaTab uTabs[i]!))

@[expose] def sigmaTxyOK : Bool :=
  sigmaTxyWords.length == 5 &&
    (List.range 5).all fun j =>
      tblEq deg (conjT deg sigmaTab sigmaTab txyTabs[j]!) (wordT deg txyLet sigmaTxyWords[j]!)

@[expose] def abInvTabs : Array Table := #[uInvTabs[0]!, uInvTabs[3]!]

@[expose] def autX : List Table := enumY.1.toList.filter (ordTest deg 2)

@[expose] def autY : List Table := enumY.1.toList.filter (ordTest deg 12)

@[expose] def pairLet (x y xi yi : Table) (l : Int) : Table :=
  if l = 1 then x else if l = -1 then xi else if l = 2 then y else yi

@[expose] def relTest (x y : Table) : Bool :=
  let xi := invT deg x
  let yi := invT deg y
  invOK deg x xi && invOK deg y yi &&
    autRelators.all (fun w => powFixW deg (w.map (pairLet x y xi yi)) 1) &&
    autWitnesses.all (fun w => !powFixW deg (w.map (pairLet x y xi yi)) 1)

@[expose] def classCap : Nat := 5000

@[expose] def autCount : Nat :=
  ((classes deg abTabs abInvTabs autX classCap).map fun c =>
    c.2.1.size * autY.countP (relTest c.1)).sum

@[expose] def autOK : Bool :=
  classOK deg abTabs abInvTabs autX classCap && autCount ≤ 699840 &&
    ordTest deg 2 abTabs[0]! && ordTest deg 12 abTabs[1]! && relTest abTabs[0]! abTabs[1]!

@[expose] def yCheck : Bool :=
  tablesOK && erelOK && genOK && yEnumOK && yCenterOK && txyEnumOK && normSweepOK && outerOK &&
    sigmaTxyOK && autOK

end CFSG.Sporadic.Recognition.LyonsSims.Ly1080
