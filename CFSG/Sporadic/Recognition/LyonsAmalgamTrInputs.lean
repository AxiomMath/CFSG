module

public import CFSG.Sporadic.Recognition.LyonsAmalgamTrData
public import CFSG.Sporadic.Recognition.LyonsAmalgamYData
public import CFSG.Sporadic.SmallOddCore.LocalCheck
public meta import CFSG.Sporadic.Recognition.LyonsAmalgamTrData
public meta import CFSG.Sporadic.Recognition.LyonsAmalgamYData
public meta import CFSG.Sporadic.SmallOddCore.LocalCheck

public section

namespace CFSG.Sporadic.Recognition.LyonsSims.Ly243

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native

abbrev deg : Nat := 243

@[expose] def genTabs : Array Table := Array.ofFn (n := 5) fun i => hexT 2 deg (deg * i.val) genHex

@[expose] def genInvTabs : Array Table := genTabs.map (invT deg)

@[expose] def lineTabs : Array Table :=
  Array.ofFn (n := 3) fun i => hexT 2 deg (deg * i.val) lineHex

@[expose] def lineInvTabs : Array Table := lineTabs.map (invT deg)

@[expose] def trLet (l : Int) : Table :=
  if 0 < l then genTabs[l.toNat - 1]! else genInvTabs[(-l).toNat - 1]!

@[expose] def txyTabs : Array Table := txyWords.toArray.map (wordT deg trLet)

@[expose] def txyInvTabs : Array Table := txyTabs.map (invT deg)

@[expose] def txyLet (l : Int) : Table :=
  if 0 < l then txyTabs[l.toNat - 1]! else txyInvTabs[(-l).toNat - 1]!

@[expose] def repTabs : Array Table := repWords.toArray.map (wordT deg trLet)

@[expose] def inLine (z a ai : Table) : Bool := tblEq deg z a || tblEq deg z ai

@[expose] def wordsOK : Bool :=
  txyWords.all (fun w => w.all fun l => l != 0 && l.natAbs ≤ 4) &&
    repWords.all (fun w => w.all fun l => l != 0 && l.natAbs ≤ 5) &&
    CFSG.Sporadic.Recognition.LyonsSims.Ly1080.sigmaTxyWords.all
      (fun w => w.all fun l => l != 0 && l.natAbs ≤ 5)

@[expose] def lineDataOK : Bool :=
  (List.range 3).all (fun i => ordTest deg 3 lineTabs[i]!) &&
    (List.range 3).all fun i => (List.range 3).all fun j =>
      i == j || !inLine lineTabs[j]! lineTabs[i]! lineInvTabs[i]!

@[expose] def tablesOK : Bool :=
  genTabs.size == 5 && lineTabs.size == 3 && txyTabs.size == 5 && repTabs.size == 6 && wordsOK &&
    (genTabs.toList ++ lineTabs.toList ++ txyTabs.toList ++ repTabs.toList).all
      (fun T => permOK deg T && invOK deg T (invT deg T)) && lineDataOK

@[expose] def conjA (g gi a : Table) : Table := conjT deg g gi a

@[expose] def permutesOK : Bool :=
  (List.range 5).all fun m =>
    (List.range 3).all fun i => (List.range 3).any fun j =>
      inLine (conjA genTabs[m]! genInvTabs[m]! lineTabs[i]!) lineTabs[j]! lineInvTabs[j]!

@[expose] def fixZeroOK : Bool :=
  (List.range 4).all fun m =>
    inLine (conjA genTabs[m]! genInvTabs[m]! lineTabs[0]!) lineTabs[0]! lineInvTabs[0]!

@[expose] def kSwapOK : Bool :=
  inLine (conjA genTabs[4]! genInvTabs[4]! lineTabs[0]!) lineTabs[1]! lineInvTabs[1]! &&
    inLine (conjA genTabs[4]! genInvTabs[4]! lineTabs[1]!) lineTabs[0]! lineInvTabs[0]! &&
    inLine (conjA genTabs[4]! genInvTabs[4]! lineTabs[2]!) lineTabs[2]! lineInvTabs[2]!

@[expose] def txyKerOK : Bool :=
  (List.range 5).all fun j => (List.range 3).all fun i =>
    inLine (conjA txyTabs[j]! txyInvTabs[j]! lineTabs[i]!) lineTabs[i]! lineInvTabs[i]!

@[expose] def txyCap : Nat := 5000

@[expose] def txyEnum : Array Table × Array Nat × Array Nat :=
  mulClosureH deg txyTabs.toList.toArray txyCap

@[expose] def txyEnumOK : Bool := CFSG.Sporadic.SmallOddCore.enumOK deg txyCap 3888 txyTabs.toList

@[expose] def txyCenterOK : Bool :=
  txyEnum.1.all fun x => !(txyTabs.all fun g => commTT deg x g) || tblEq deg x (idT deg)

@[expose] def fixesLines (z : Table) : Bool :=
  let zi := invT deg z
  (List.range 3).all fun i => inLine (conjA z zi lineTabs[i]!) lineTabs[i]! lineInvTabs[i]!

@[expose] def cosetOK : Bool :=
  tblEq deg repTabs[0]! (idT deg) &&
    (List.range 6).all (fun i => (genTabs.toList ++ genInvTabs.toList).all fun g =>
      (List.range 6).any fun j =>
        memT deg txyEnum.1 (compT deg (compT deg repTabs[i]! g) (invT deg repTabs[j]!))) &&
    (List.range 6).all fun j => j == 0 || !fixesLines repTabs[j]!

@[expose] def kCompatOK : Bool :=
  CFSG.Sporadic.Recognition.LyonsSims.Ly1080.sigmaTxyWords.length == 5 &&
    (List.range 5).all fun j =>
      tblEq deg (conjT deg genTabs[4]! genInvTabs[4]! txyTabs[j]!)
        (wordT deg txyLet CFSG.Sporadic.Recognition.LyonsSims.Ly1080.sigmaTxyWords[j]!)

@[expose] def trCheck : Bool :=
  tablesOK && permutesOK && fixZeroOK && kSwapOK && txyKerOK && txyEnumOK && txyCenterOK &&
    cosetOK && kCompatOK

end CFSG.Sporadic.Recognition.LyonsSims.Ly243
