module

public import CFSG.Assembly.Defs
public import CFSG.Sporadic.FischerOddCore.Fi22Cent
public import CFSG.Sporadic.FischerOddCore.Fi22ExtSylowCheckInputs
public import CFSG.Sporadic.SmallOddCore.LocalCheck
public import Certificates.Data.CFSGNative.Schreier.SetOrbit

public section

namespace CFSG.Monster.B.Fischer

open CFSG.Certificates CFSG.Certificates.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.Th.Native CFSG.Sporadic.FischerOddCore CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.SmallOddCore.Native

@[expose] def fi22NineD1 : Nat := 1122

@[expose] def fi22NineD2 : Nat := 1226

@[expose] def fi22NineO2 : List Nat := [1122, 1226]

@[expose] def fi22NineO4 : List Nat := [1920, 2321, 2506, 2743]

@[expose] def fi22NineX0 : List Nat := [1122, 1226, 1920, 2321, 2506, 2743]

@[expose] def fi22NineO16 : List Nat :=
  [63, 244, 512, 650, 1033, 1405, 1762, 1925, 2058, 2313, 2483, 2501, 2620, 3359, 3416, 3446]

@[expose] def fi22NineX1 : List Nat :=
  [63, 244, 512, 650, 1033, 1122, 1226, 1405, 1762, 1925, 2058, 2313, 2483, 2501, 2620, 3359,
    3416, 3446]

@[expose] def fi22NineBasePts : List Nat := [0, 1, 2, 3, 6, 4]

@[expose] def fi22NinePTbls (_ : Unit := ()) : Array Table :=
  fi22OrigArrs.map fun a => a.map UInt32.ofNat

@[expose] def fi22NinePGens (_ : Unit := ()) : List Table :=
  (fi22NinePTbls ()).toList

@[expose] def fi22NineUTbls (_ : Unit := ()) : Array Table :=
  ((fi22OuterStrong3510 4).extract 0 9).map fun a => a.map UInt32.ofNat

@[expose] def fi22NineH1Tbls (_ : Unit := ()) : Array Table :=
  ((fi22CentStrong 1).extract 0 9).map fun a => a.map UInt32.ofNat

@[expose] def fi22NineH1Gens (_ : Unit := ()) : List Table :=
  (fi22NineH1Tbls ()).toList

@[expose] def fi22NineZTbl (_ : Unit := ()) : Table := (fi22ExtArr 22).map UInt32.ofNat

@[expose] def fi22NineUTbl (_ : Unit := ()) : Table := fi22GraphOuterArr.map UInt32.ofNat

@[expose] def fi22NineXWord : List Nat :=
  [  8, 6, 5, 9, 9, 8, 8, 8, 8, 8, 8, 8, 8, 8, 4, 1, 4, 4, 4, 4, 4, 4, 4, 4, 4, 9, 8, 5, 6, 2, 1, 3,
  7, 2, 2, 2, 2, 2, 2, 7, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3]

@[expose] def fi22NineYWord : List Nat :=
  [  1, 3, 2, 2, 2, 8, 2, 4, 4, 4, 4, 4, 4, 4, 4, 4, 9, 9, 9, 9, 3, 3, 2, 4, 4, 4, 4, 4, 4, 4, 4, 4,
  9, 8, 5, 6, 2]

@[expose] def fi22NineAWord : List Nat :=
  [  6, 4, 8, 2, 2, 2, 7, 4, 3, 8, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3, 2, 2, 2, 7, 2, 3, 3, 3, 3, 3, 3, 3,
  3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8,
  8, 8, 4]

@[expose] def fi22NineGWord : List Nat :=
  [  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  2, 2, 2, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 2,
  2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 2, 2, 1, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2,
  2, 2, 2, 2, 2, 2, 2, 1, 2, 1, 2, 2, 2, 2, 1, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  2, 1, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 1, 2, 2, 2, 2, 2, 1, 2,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2,
  2, 1, 2, 1, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 1, 2, 2, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2,
  2, 2, 2, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  2, 2, 2, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 1, 2, 2, 2, 2,
  2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 2, 2, 2,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 1, 2, 2, 2, 2, 2, 1, 2, 2,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2,
  2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 1, 2, 1, 2, 2, 2,
  2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 2, 2, 1,
  2, 2, 2, 2, 1, 2, 2, 2, 2, 1, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  2, 2, 2, 2, 1, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  2, 2, 1, 2, 1, 2, 2, 2, 2, 1, 2, 2, 2, 2, 1, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 1, 2, 2, 2, 2, 1, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  2, 2, 2, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2]

@[expose] def fi22NinePWord : List Nat :=
  [  1, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  1, 2, 1, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 1, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 1, 2, 1, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2,
  2]

@[expose] def fi22NineH0Word : List Nat :=
  [  2, 2, 2, 7, 6, 1, 8, 8, 8, 8, 8, 8, 8, 8, 8, 9, 9, 9, 9, 9, 9, 9, 9, 7, 4, 4, 4, 4, 4, 4, 4, 4,
  4, 7, 9, 7, 9, 1, 3, 7, 2, 2, 2, 2, 2, 2, 7, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3]

@[expose] def fi22NineH1Word : List Nat :=
  [  3, 7, 2, 2, 7, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 1, 9, 9, 9, 9, 7, 9, 9, 9, 9, 7, 9, 9, 9, 9, 4,
  4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3, 6, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 2,
  2, 8, 8, 8, 8, 8, 8, 8, 8, 8]

@[expose] def fi22NineXTbl (_ : Unit := ()) : Table :=
  wordTbl 3510 (fi22NineH1Gens ()) fi22NineXWord

@[expose] def fi22NineYTbl (_ : Unit := ()) : Table :=
  wordTbl 3510 (fi22NineH1Gens ()) fi22NineYWord

@[expose] def fi22NineATbl (_ : Unit := ()) : Table :=
  wordTbl 3510 (fi22NineH1Gens ()) fi22NineAWord

@[expose] def fi22NinePWordTbl (_ : Unit := ()) : Table :=
  wordTbl 3510 (fi22NinePGens ()) fi22NinePWord

@[expose] def fi22NineGTbl (_ : Unit := ()) : Table :=
  wordTbl 3510 (fi22NinePGens ()) fi22NineGWord

@[expose] def fi22NineH0Tbl (_ : Unit := ()) : Table :=
  wordTbl 3510 (fi22NineH1Gens ()) fi22NineH0Word

@[expose] def fi22NineH1Tbl (_ : Unit := ()) : Table :=
  wordTbl 3510 (fi22NineH1Gens ()) fi22NineH1Word

@[expose] def fi22NineSTbl (_ : Unit := ()) : Table :=
  compT 3510 (compT 3510 (fi22NineUTbl ()) (fi22NinePWordTbl ())) (fi22NineH0Tbl ())

@[expose] def fi22NineS1Tbl (_ : Unit := ()) : Table :=
  compT 3510 (compT 3510 (fi22NineUTbl ()) (fi22NinePWordTbl ())) (fi22NineH1Tbl ())

@[expose] def fi22NineUFixCheck (_ : Unit := ()) : Bool :=
  (List.range 9).all fun i =>
    decide (imgSorted ((fi22OuterStrong3510 4)[i]!) fi22NineX0 = fi22NineX0)

@[expose] def fi22NineShapeCheck (_ : Unit := ()) : Bool :=
  decide ((fi22NinePTbls ()).size = 2) && decide ((fi22NineUTbls ()).size = 9) &&
    decide ((fi22NineH1Tbls ()).size = 9) && decide ((fi22NineH1Gens ()).length = 9) &&
    decide ((fi22NinePGens ()).length = 2) && decide ((fi22CentStrong 1).size = 16)

@[expose] def fi22NineWordCheck (_ : Unit := ()) : Bool :=
  [fi22NineXWord, fi22NineYWord, fi22NineAWord, fi22NineH0Word, fi22NineH1Word].all
      (fun w => w.all fun l => decide (1 ≤ l ∧ l ≤ 9)) &&
    [fi22NinePWord, fi22NineGWord].all (fun w => w.all fun l => decide (1 ≤ l ∧ l ≤ 2))

@[expose] def fi22NineXYCheck (_ : Unit := ()) : Bool :=
  let X := fi22NineXTbl ()
  let Y := fi22NineYTbl ()
  permOK 3510 X && permOK 3510 Y &&
    tblEq 3510 (powT 3510 3 X) (idT 3510) && tblEq 3510 (powT 3510 3 Y) (idT 3510) &&
    tblEq 3510 (compT 3510 X Y) (compT 3510 Y X) &&
    !tblEq 3510 X (idT 3510) && !tblEq 3510 Y (idT 3510) && !tblEq 3510 Y X &&
    !tblEq 3510 Y (compT 3510 X X) &&
    decide (imgSorted (natArr X) fi22NineX0 = fi22NineX0) &&
    decide (imgSorted (natArr Y) fi22NineX0 = fi22NineX0)

@[expose] def fi22NineACheck (_ : Unit := ()) : Bool :=
  let A := fi22NineATbl ()
  permOK 3510 A && tblEq 3510 (powT 3510 3 A) (idT 3510) && !tblEq 3510 A (idT 3510) &&
    decide (imgSorted (natArr A) fi22NineX1 = fi22NineX1)

@[expose] def fi22NineInvertCheck (_ : Unit := ()) : Bool :=
  let A := fi22NineATbl ()
  let G := fi22NineGTbl ()
  permOK 3510 G && invOK 3510 G (invT 3510 G) && permOK 3510 A && invOK 3510 A (invT 3510 A) &&
    tblEq 3510 (compT 3510 (compT 3510 G A) (invT 3510 G)) (invT 3510 A)

@[expose] def fi22NineSCheck (_ : Unit := ()) : Bool :=
  let S := fi22NineSTbl ()
  let S1 := fi22NineS1Tbl ()
  let Z := fi22NineZTbl ()
  permOK 3510 S && permOK 3510 S1 && permOK 3510 Z &&
    tblEq 3510 (compT 3510 S Z) (compT 3510 Z S) &&
    tblEq 3510 (compT 3510 S1 Z) (compT 3510 Z S1) &&
    decide (imgSorted (natArr S) fi22NineX0 = fi22NineX0) &&
    decide (imgSorted (natArr S1) fi22NineX1 = fi22NineX1) &&
    decide (imgSorted (natArr S1) fi22NineX0 = fi22NineX0) &&
    decide (natArr (fi22NineZTbl ()) = fi22ExtArr 22)

@[expose] def fi22NineOrbit0 (_ : Unit := ()) : Array (List Nat) × Array Nat × Array Nat :=
  translateSearch ((fi22CentStrong 1).extract 0 9) fi22NineX0 45

@[expose] def fi22NineOrbit1 (_ : Unit := ()) : Array (List Nat) × Array Nat × Array Nat :=
  translateSearch ((fi22CentStrong 1).extract 0 9) fi22NineX1 135

@[expose] def fi22NineFixCount (gens : Array (Array Nat)) (sets : Array (List Nat)) : Nat :=
  (sets.toList.filter fun s => gens.all fun g => imgSorted g s == s).length

@[expose] def fi22NineOrbitCheck0 (_ : Unit := ()) : Bool :=
  let O := fi22NineOrbit0 ()
  O.1.size == 45 && decide (O.1.toList.Nodup) &&
    translatesOK ((fi22CentStrong 1).extract 0 9) fi22NineX0 O.1 O.2.1 O.2.2 &&
    decide (fi22NineFixCount ((fi22OuterStrong3510 4).extract 0 9) O.1 = 1)

@[expose] def fi22NineOrbitCheck1 (_ : Unit := ()) : Bool :=
  let O := fi22NineOrbit1 ()
  O.1.size == 135 && decide (O.1.toList.Nodup) &&
    translatesOK ((fi22CentStrong 1).extract 0 9) fi22NineX1 O.1 O.2.1 O.2.2 &&
    decide (fi22NineFixCount ((fi22OuterStrong3510 4).extract 0 9) O.1 = 1)

@[expose] def fi22NineIsCentral (a b c : Nat) : Bool :=
  let U := fi22NineUTbls ()
  (List.range 9).all fun i =>
    (List.range 6).all fun j =>
      decide (tr3 fi22TLevels a b c (ap (U.getD i (idT 3510)) (fi22NineBasePts.getD j 0)) =
        ap (U.getD i (idT 3510)) (tr3 fi22TLevels a b c (fi22NineBasePts.getD j 0)))

@[expose] def fi22NineZBase (_ : Unit := ()) : List Nat :=
  fi22NineBasePts.map fun b => ap (fi22NineZTbl ()) b

@[expose] def fi22NineCenterCheck (_ : Unit := ()) : Bool :=
  let zB := fi22NineZBase ()
  (List.range 131072).all fun t =>
    let a := t / 128
    let b := (t / 4) % 32
    let c := t % 4
    let bi := fi22NineBasePts.map fun p => tr3 fi22TLevels a b c p
    !fi22NineIsCentral a b c || decide (bi = fi22NineBasePts) || decide (bi = zB)

@[expose] def fi22NineZMemCheck (_ : Unit := ()) : Bool := fi22InT (fi22ExtArr 22)

@[expose] def fi22NineCentralIdx (_ : Unit := ()) : List Nat :=
  (List.range 131072).filter fun t =>
    fi22NineIsCentral (t / 128) ((t / 4) % 32) (t % 4)

@[expose] def fi22NineCentralIdxCheck (_ : Unit := ()) : Bool :=
  decide ((fi22NineCentralIdx ()).length = 2) && decide (0 ∈ fi22NineCentralIdx ())

@[expose] def fi22NineUFix1Check (_ : Unit := ()) : Bool :=
  (List.range 9).all fun i =>
    decide (imgSorted ((fi22OuterStrong3510 4)[i]!) fi22NineX1 = fi22NineX1)

@[expose] def fi22NineBridgeCheck (_ : Unit := ()) : Bool :=
  (List.range 9).all
      (fun i => decide (natArr ((fi22NineH1Tbls ())[i]!) = (fi22CentStrong 1)[i]!)) &&
    (List.range 9).all
      (fun i => decide (natArr ((fi22NineUTbls ())[i]!) = (fi22OuterStrong3510 4)[i]!)) &&
    decide (natArr ((fi22NinePTbls ())[0]!) = fi22ChainGen 0) &&
    decide (natArr ((fi22NinePTbls ())[1]!) = fi22ChainGen 1)

@[expose] def fi22NineGenPermCheck (_ : Unit := ()) : Bool :=
  (fi22NinePTbls ()).toList.all (fun g => permOK 3510 g) &&
    (fi22NineUTbls ()).toList.all (fun g => permOK 3510 g) &&
    (fi22NineH1Tbls ()).toList.all (fun g => permOK 3510 g)

theorem fi22NineH1Tbls_eq :
    fi22NineH1Tbls () =
      ((fi22CentStrong 1).extract 0 9).map (fun a => a.map UInt32.ofNat) := rfl

theorem fi22NinePTbls_eq :
    fi22NinePTbls () = fi22OrigArrs.map (fun a => a.map UInt32.ofNat) := rfl

theorem fi22NineH1Gens_eq : fi22NineH1Gens () = (fi22NineH1Tbls ()).toList := rfl

theorem fi22NinePGens_eq : fi22NinePGens () = (fi22NinePTbls ()).toList := rfl

theorem fi22NineUTbls_eq :
    fi22NineUTbls () =
      ((fi22OuterStrong3510 4).extract 0 9).map (fun a => a.map UInt32.ofNat) := rfl

theorem fi22NineZTbl_eq : fi22NineZTbl () = (fi22ExtArr 22).map UInt32.ofNat := rfl

@[expose] def fi22NineOuterCheck (_ : Unit := ()) : Bool :=
  decide (natArr (fi22NineUTbl ()) = fi22GraphOuterArr) && permOK 3510 (fi22NineUTbl ()) &&
    fi22InP (natArr (compT 3510 (fi22NineUTbl ()) (fi22NineSTbl ()))) &&
    fi22InP (natArr (compT 3510 (fi22NineUTbl ()) (fi22NineS1Tbl ())))

@[expose] def fi22NineZCommCheck (_ : Unit := ()) : Bool :=
  let U := fi22NineUTbls ()
  (List.range 9).all fun i => tblEq 3510 (compT 3510 U[i]! (fi22NineZTbl ()))
    (compT 3510 (fi22NineZTbl ()) U[i]!)

@[expose] def fi22NineCheck (_ : Unit := ()) : Bool :=
  fi22NineXYCheck () && fi22NineACheck () && fi22NineInvertCheck () && fi22NineSCheck () &&
    fi22NineZMemCheck () && fi22NineOrbitCheck0 () && fi22NineOrbitCheck1 () &&
    fi22NineCenterCheck () && fi22NineZCommCheck () && fi22NineGenPermCheck () &&
    fi22NineBridgeCheck () && fi22NineWordCheck () && fi22NineShapeCheck () &&
    fi22NineUFixCheck () && fi22NineCentralIdxCheck () && fi22NineUFix1Check () &&
    fi22NineOuterCheck ()

end CFSG.Monster.B.Fischer
