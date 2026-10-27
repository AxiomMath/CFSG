module

public import Certificates.Data.RouteP.Objects

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom.Native

open CFSG.Sporadic.Th.Native
open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native

set_option compiler.extract_closed false

@[expose] def geomReps : Array Nat := #[0, 1479, 3, 750020, 750100, 1, 2]

@[expose] def geomLevels : Array Nat := #[0, 1, 2, 3, 3, 4, 4]

@[expose] def geomSizes : Array Nat := #[1, 31671, 825792, 31671, 31671, 1, 1]

@[expose] def geomA1Letters : Array Nat := #[6, 7, 8]

@[inline, expose] def memTree (T : CFSG.Perm.Native.Tree) (p : Nat) : Bool :=
  ap T.pos p < T.pts.size && ap T.pts (ap T.pos p) == p

@[expose] def geomTrees (gs : Array Table) : Array CFSG.Perm.Native.Tree :=
  geomReps.map fun r => CFSG.Perm.Native.treeBFS degree r gs zpLetters

@[expose] def firstTree (trees : Array CFSG.Perm.Native.Tree) (v : Nat) : Nat := Id.run do
  for i in [0:7] do
    if memTree trees[i]! v then return i
  return 7

@[expose] def geomLab (trees : Array CFSG.Perm.Native.Tree) : Table :=
  Array.ofFn (n := degree) fun v => UInt32.ofNat (firstTree trees v.val)

@[expose] def zpTreesOK (gs : Array Table) (trees : Array CFSG.Perm.Native.Tree) : Bool :=
  trees.size == 7 && allIn 0 7 fun i =>
    trees[i]!.pts.size == geomSizes[i]! &&
      CFSG.Perm.Native.treeOK degree geomReps[i]! trees[i]! gs zpLetters

@[expose] def labOK (gs : Array Table) (trees : Array CFSG.Perm.Native.Tree) (lab : Table) :
    Bool :=
  allIn 0 7 (fun i => ap lab geomReps[i]! == i) &&
    allIn 0 degree (fun v => decide (ap lab v < 7) && memTree trees[ap lab v]! v) &&
    zpLetters.all fun l =>
      let g := gs[l]!
      allIn 0 degree fun v => ap lab (ap g v) == ap lab v

@[expose] def treeWord (T : CFSG.Perm.Native.Tree) (p : Nat) : List Int := Id.run do
  let mut w : List Int := []
  let mut k := ap T.pos p
  for _ in [0:degree] do
    if 0 < k then
      w := w ++ [Int.ofNat (ap T.lab k) + 1]
      k := ap T.par k
    else break
  return w

@[expose] def geomWords (ms : Array Table) : Array (List Int) :=
  let T := CFSG.Perm.Native.treeBFS degree 0 ms #[0, 1]
  geomReps.map fun r => treeWord T r

@[expose] def repTabs (ms : Array Table) (words : Array (List Int)) : Array Table :=
  let msInv := ms.map (invT degree)
  words.map fun w => wordT degree (letterTab degree ms msInv) w

@[expose] def distOK (lab : Table) (tabs : Array Table) (gamma : Table) : Bool :=
  tabs.size == 7 && geomLevels[0]! == 0 &&
    allIn 0 7 (fun i => geomLevels[i]! != 0 || geomReps[i]! == 0) &&
    allIn 0 7 fun i =>
      let T := tabs[i]!
      let k := geomLevels[i]!
      ap T 0 == geomReps[i]! &&
        (k == 0 || gamma.any fun c => geomLevels[ap lab (ap T c.toNat)]! + 1 == k) &&
        gamma.all fun c => decide (geomLevels[ap lab (ap T c.toNat)]! ≤ k + 1)

@[expose] def s1OK (objs : Array Table) (trees : Array CFSG.Perm.Native.Tree)
    (atree : CFSG.Perm.Native.Tree) : Bool :=
  geomA1Letters.all (fun l => ap objs[l]! 0 == 0 && ap objs[l]! 1479 == 1479) &&
    atree.pts.size == 3510 &&
    CFSG.Perm.Native.treeOK degree 99705 atree objs geomA1Letters &&
    let G0 := trees[1]!
    let tau := objs[tauReg]!
    G0.pts.all fun c =>
      let w := ap tau c.toNat
      !memTree G0 w || memTree atree w

@[expose] def geomOKAt (gs objs ms : Array Table) (trees : Array CFSG.Perm.Native.Tree)
    (lab : Table) (words : Array (List Int)) (atree : CFSG.Perm.Native.Tree) : Bool :=
  words.size == 7 && zpTreesOK gs trees && labOK gs trees lab &&
    distOK lab (repTabs ms words) trees[1]!.pts && s1OK objs trees atree

@[expose] def geomOK (_ : Unit := ()) : Bool :=
  let gs := genTabs ()
  let objs := (objRun ()).1
  let ms := mTabs ()
  let trees := geomTrees gs
  geomOKAt gs objs ms trees (geomLab trees) (geomWords ms)
    (CFSG.Perm.Native.treeBFS degree 99705 objs geomA1Letters)

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom.Native
