module

public import Certificates.Data.CFSGNative.Fi23.Classes

public section

namespace CFSG.Sporadic.Fi23

open CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.Sporadic.Fi23.Native

@[expose] def nineCWord : List Int := [8, 8, 8, 2, 2, 13, 11, 8, 4]

@[expose] def nineE : Nat := 28381

@[expose] def nineF : Nat := 8514

@[expose] def nineO4 : List Nat := [8514, 12009, 15862, 20635]

@[expose] def nineRoots : Array Nat :=
  #[0, 1, 8514, 2, 3, 4, 5, 6, 8, 11, 16, 19, 25, 30, 33, 34, 39, 93, 102, 954, 3127]

@[expose] def nineHWords : Array (List Int) :=
  #[[11, 19, 16, 16, 22, 8, 15], [11, 13, 14, 13, 18, 15, 15], [8, 10, 12, 13, 11, 9]]

@[expose] def nineXWord : List Int :=
  [11, 19, 16, 16, 22, 8, 15, 14, 14, 19, 12, 15, 12, 10, 14, 14, 19, 12, 15, 12, 10, 11, 19, 16,
    16, 22, 8, 15, 11, 13, 14, 13, 18, 15, 15, 11, 13, 14, 13, 18, 15, 15, 11, 13, 14, 13, 18, 15,
    15, 11, 19, 16, 16, 22, 8, 15, 14, 14, 19, 12, 15, 12, 10, 14, 14, 19, 12, 15, 12, 10, 14, 14,
    19, 12, 15, 12, 10, 14, 9, 23, 17, 17, 18, 10, 11, 13, 14, 13, 18, 15, 15, 11, 13, 14, 13, 18,
    15, 15, 14, 9, 23, 17, 17, 18, 10]

@[expose] def nineXExp : Nat := 2

@[expose] def nineYWord : List Int :=
  [11, 19, 16, 16, 22, 8, 15, 14, 14, 19, 12, 15, 12, 10, 14, 14, 19, 12, 15, 12, 10, 11, 19, 16,
    16, 22, 8, 15, 11, 13, 14, 13, 18, 15, 15, 11, 13, 14, 13, 18, 15, 15, 14, 9, 23, 17, 17, 18,
    10, 14, 14, 19, 12, 15, 12, 10, 11, 19, 16, 16, 22, 8, 15, 14, 14, 19, 12, 15, 12, 10, 11, 19,
    16, 16, 22, 8, 15, 11, 13, 14, 13, 18, 15, 15, 11, 19, 16, 16, 22, 8, 15, 14, 14, 19, 12, 15,
    12, 10, 14, 14, 19, 12, 15, 12, 10, 11, 19, 16, 16, 22, 8, 15, 11, 13, 14, 13, 18, 15, 15, 11,
    13, 14, 13, 18, 15, 15, 14, 9, 23, 17, 17, 18, 10, 14, 14, 19, 12, 15, 12, 10, 11, 19, 16, 16,
    22, 8, 15, 14, 14, 19, 12, 15, 12, 10, 11, 19, 16, 16, 22, 8, 15, 11, 13, 14, 13, 18, 15, 15,
    11, 19, 16, 16, 22, 8, 15, 14, 14, 19, 12, 15, 12, 10, 14, 14, 19, 12, 15, 12, 10, 11, 19, 16,
    16, 22, 8, 15, 11, 13, 14, 13, 18, 15, 15, 11, 13, 14, 13, 18, 15, 15, 11, 13, 14, 13, 18, 15,
    15, 11, 19, 16, 16, 22, 8, 15, 14, 14, 19, 12, 15, 12, 10, 14, 14, 19, 12, 15, 12, 10, 14, 14,
    19, 12, 15, 12, 10, 14, 9, 23, 17, 17, 18, 10, 11, 13, 14, 13, 18, 15, 15, 11, 13, 14, 13, 18,
    15, 15, 14, 9, 23, 17, 17, 18, 10, 11, 19, 16, 16, 22, 8, 15, 14, 14, 19, 12, 15, 12, 10, 14,
    14, 19, 12, 15, 12, 10, 11, 19, 16, 16, 22, 8, 15, 11, 13, 14, 13, 18, 15, 15, 11, 13, 14, 13,
    18, 15, 15, 14, 9, 23, 17, 17, 18, 10, 14, 14, 19, 12, 15, 12, 10, 11, 19, 16, 16, 22, 8, 15,
    14, 14, 19, 12, 15, 12, 10, 11, 19, 16, 16, 22, 8, 15, 11, 13, 14, 13, 18, 15, 15, 11, 19, 16,
    16, 22, 8, 15, 14, 14, 19, 12, 15, 12, 10, 14, 14, 19, 12, 15, 12, 10, 11, 19, 16, 16, 22, 8,
    15, 11, 13, 14, 13, 18, 15, 15, 11, 13, 14, 13, 18, 15, 15, 14, 9, 23, 17, 17, 18, 10, 14, 14,
    19, 12, 15, 12, 10, 11, 19, 16, 16, 22, 8, 15, 14, 14, 19, 12, 15, 12, 10, 11, 19, 16, 16, 22,
    8, 15, 11, 13, 14, 13, 18, 15, 15]

@[expose] def nineYExp : Nat := 4

@[expose] def nineMaps (T : Table) (l : List Nat) : Bool := l.all fun q => l.contains (ap T q)

@[expose] def nineWordsLt (m : Nat) : Bool :=
  (nineCWord :: nineXWord :: nineYWord :: nineHWords.toList).all fun w => w.all fun z => z.toNat < m

@[expose] def nineULetters (LS : Array Table) (C Ci : Table) : Array Table :=
  LS.map fun t => compT 31671 Ci (compT 31671 t C)

@[expose] def nineUTrees (UL : Array Table) : Array Tree :=
  nineRoots.map fun r => treeBFS 31671 r UL (Array.range UL.size)

@[expose] def nineUCheck (UL : Array Table) : Bool :=
  let lv := Array.range UL.size
  let UT := nineUTrees UL
  allIn 0 nineRoots.size (fun i => CFSG.Perm.Native.treeOK 31671 nineRoots[i]! UT[i]! UL lv) &&
    UT[0]!.pts.size == 1 &&
    UT[1]!.pts.size == 2 && [1, nineE].all (inTreeB UT[1]!) &&
    UT[2]!.pts.size == 4 && nineO4.all (inTreeB UT[2]!) &&
    allIn 3 nineRoots.size (fun i => 8 ≤ UT[i]!.pts.size) &&
    allIn 0 31671 (fun p => UT.any fun T => inTreeB T p)

@[expose] def nineLevelCheck (L : Array Table) : Bool :=
  let lv := levelLetters L chainBase 2
  let T := treeBFS 31671 nineE L lv
  CFSG.Perm.Native.treeOK 31671 nineE T L lv && T.pts.size == 693

@[expose] def nineHLetters (L : Array Table) : Array Table :=
  buildLetters 31671 (jGen L) nineHWords

@[expose] def nineHCheck (L : Array Table) : Bool :=
  let HL := nineHLetters L
  let lv := Array.range HL.size
  let T := treeBFS 31671 nineF HL lv
  allIn 0 nineHWords.size (fun j => invOK 31671 HL[2 * j]! HL[2 * j + 1]! &&
      ap HL[2 * j]! 0 == 0 && ap HL[2 * j]! 1 == 1 && ap HL[2 * j]! nineE == nineE) &&
    CFSG.Perm.Native.treeOK 31671 nineF T HL lv && T.pts.size == 180

@[expose] def nineXTable (L : Array Table) : Table :=
  powT 31671 nineXExp (wordT 31671 (jGen L) nineXWord)

@[expose] def nineYTable (L : Array Table) : Table :=
  powT 31671 nineYExp (wordT 31671 (jGen L) nineYWord)

@[expose] def nineXYCheck (X Y : Table) : Bool :=
  let X2 := compT 31671 X X
  ap X 0 == 0 && nineMaps X [1, nineE] && nineMaps X nineO4 && order3OK 31671 X && !isIdT X &&
    ap Y 0 == 0 && nineMaps Y [1, nineE] && nineMaps Y nineO4 && order3OK 31671 Y && !isIdT Y &&
    allIn 0 31671 (fun i => ap X (ap Y i) == ap Y (ap X i)) &&
    !allIn 0 31671 (fun i => ap Y i == ap X i) && !allIn 0 31671 (fun i => ap Y i == ap X2 i)

@[expose] def nineCheck (O : WOrbit) : Bool :=
  let L := chainLetters O
  let C := wordT 31671 (jGen L) nineCWord
  let Ci := invT 31671 C
  nineWordsLt L.size && invOK 31671 C Ci && nineUCheck (nineULetters (sylLetters L) C Ci) &&
    nineLevelCheck L && nineHCheck L && nineXYCheck (nineXTable L) (nineYTable L)

@[expose] def fi23IndexNineCheck (_ : Unit := ()) : Bool := nineCheck (orbitData ())

end CFSG.Sporadic.Fi23
