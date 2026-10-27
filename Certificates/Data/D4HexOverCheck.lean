module

public import Certificates.Data.D4HexLinkCheck
public import Certificates.Data.D4HexOverWords
public import CFSG.Sporadic.Schreier.TitsOrbit
public import CFSG.Quasithin.Recognition.CertMergeTargets
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.Sporadic.Schreier.TitsBasic

public section

namespace CFSG.D4Hex

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits CFSG.Certificates
  CFSG.Certificates.Native CFSG.Quasithin

@[expose] def flagGen (j c : Nat) : Nat :=
  let l := c / 3
  let p' := (permArrs[j]!)[lnPt l (c % 3)]!
  let l' := lineIndex.getD (imgKey j l) 0
  3 * l' + (if lnPt l' 0 = p' then 0 else if lnPt l' 1 = p' then 1 else 2)

@[expose] def flagArr (j : Nat) : Array Nat := Array.ofFn (n := 7371) fun c => flagGen j c.val

@[expose] def flagArrs : Array (Array Nat) := Array.ofFn (n := 8) fun j => flagArr j.val

@[expose] def ptWordArr (w : List Nat) : Array Nat :=
  w.foldr (fun k acc => compA 819 permArrs[k]! acc) (idA 819)

@[expose] def flagWordArr (w : List Nat) : Array Nat :=
  w.foldr (fun k acc => compA 7371 flagArrs[k]! acc) (idA 7371)

@[expose] def ptPowArr (a : Array Nat) : Nat → Array Nat
  | 0 => idA 819
  | k + 1 => compA 819 a (ptPowArr a k)

@[expose] def bFlagArrs : Array (Array Nat) :=
  #[flagArrs[0]!, flagArrs[1]!, flagArrs[2]!, flagArrs[6]!, flagWordArr [3, 2, 4, 2]]

@[expose] def uPtArrs : Array (Array Nat) :=
  #[permArrs[0]!, permArrs[1]!, permArrs[2]!, permArrs[6]!]

@[expose] def ovDForest : Array Nat × Array Nat × Array Nat × Array Nat :=
  orbitForest 7371 flagArrs #[0]

@[expose] def ovBForest : Array Nat × Array Nat × Array Nat × Array Nat :=
  orbitForest 7371 bFlagArrs ovReps.toArray

@[expose] def ovUForest : Array Nat × Array Nat × Array Nat × Array Nat :=
  orbitForest 819 uPtArrs ovURep.toArray

@[expose] def ovMerge (j : Nat) : List (Fin 8 × Fin 7371 × Fin 7371) :=
  let off := (ovMergeLens.take j).foldl (· + ·) 0
  (List.range (ovMergeLens.getD j 0)).map fun r =>
    let o := 9 * (off + r)
    (finPt 8 (hexAtW ovMergeText.toUTF8 o 1), finPt 7371 (hexAtW ovMergeText.toUTF8 (o + 1) 4),
      finPt 7371 (hexAtW ovMergeText.toUTF8 (o + 5) 4))

@[expose] def ovFlagCheck : Bool :=
  flagArrs.size == 8 && bFlagArrs.size == 5 &&
  orbitLabelOK 7371 flagArrs 1 ovDForest.1 #[0] ovDForest.2.1 ovDForest.2.2.1
    ovDForest.2.2.2 &&
  ovReps.length == 12 && ovReps[0]! == 0 && ovReps[1]! == 1 && ovReps[2]! == 3 &&
  orbitLabelOK 7371 bFlagArrs 12 ovBForest.1 ovReps.toArray ovBForest.2.1 ovBForest.2.2.1
    ovBForest.2.2.2 &&
  ovBForest.1[2]! == 1 &&
  (allLt 7371 fun c => lnPt (c / 3) (c % 3) != 0 || ovBForest.1[c]! == 0 ||
    ovBForest.1[c]! == 2) &&
  ovMergeLens.length == 9 &&
  (allLt 9 fun j => mergeTargetsOK 7371 flagArrs 0 ovReps[j + 3]! (mergeVals (ovMerge j))
    [1, 3]) &&
  lnPt 1 0 == 0

@[expose] def ovUCheck : Bool :=
  uPtArrs.size == 4 && ovURep.length == 6 && ovURep[0]! == 0 && ovURep[1]! == 1 &&
  orbitLabelOK 819 uPtArrs 6 ovUForest.1 ovURep.toArray ovUForest.2.1 ovUForest.2.2.1
    ovUForest.2.2.2 &&
  ovUForest.1[5]! == 1 &&
  (List.range 6).map (labelCount 819 ovUForest.1) == [1, 2, 16, 32, 256, 512]

@[expose] def ovZetaCheck : Bool :=
  (ptWordArr [3, 2, 4, 2])[0]! == 0 && fixesLine0 (ptWordArr [3, 2, 4, 2]) &&
  ptPowArr (ptWordArr [3, 2, 4, 2]) 7 == idA 819 &&
  compA 819 (ptWordArr [3, 2, 4, 2]) permArrs[0]! == compA 819 (ptWordArr [2])
    (ptWordArr [3, 2, 4, 2]) &&
  compA 819 (ptWordArr [3, 2, 4, 2]) permArrs[1]! == compA 819 (ptWordArr [0, 1])
    (ptWordArr [3, 2, 4, 2]) &&
  compA 819 (ptWordArr [3, 2, 4, 2]) permArrs[2]! == compA 819 (ptWordArr [1, 2])
    (ptWordArr [3, 2, 4, 2]) &&
  compA 819 (ptWordArr [3, 2, 4, 2]) permArrs[6]! == compA 819 (ptWordArr [0, 2, 6, 0, 2])
    (ptWordArr [3, 2, 4, 2]) &&
  compA 819 (ptWordArr [3, 2, 4, 2]) permArrs[0]! != compA 819 permArrs[0]!
    (ptWordArr [3, 2, 4, 2]) &&
  (permArrs[7]!)[0]! != 0 && fixesLine0 permArrs[7]! &&
  (permArrs[3]!)[0]! == 0 && !fixesLine0 permArrs[3]!

@[expose] def overCheck : Bool := ovFlagCheck && ovUCheck && ovZetaCheck

end CFSG.D4Hex
