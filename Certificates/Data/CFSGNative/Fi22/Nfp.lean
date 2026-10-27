module

public import Certificates.Data.CFSGNative.Fi22.Classes
public import Certificates.Data.CFSGNative.Fi22.Centralizer
public import Certificates.Data.CFSGNative.Fi22.NfpData

public section

namespace CFSG.Sporadic.Fi22.Native

open CFSG.F3.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native

set_option compiler.extract_closed false

@[inline, expose] def tabOf (O : COrbit) (c : Nat) : Table := cTab O (genTables O (-2)) c

@[expose] def closTree (tb : Array Table) (i : Nat) : Tree :=
  treeBFS 3510 nfpBase[0]! tb (Array.range i)

@[expose] def closOK (tb : Array Table) (i : Nat) : Bool :=
  CFSG.Perm.Native.treeOK 3510 nfpBase[0]! (closTree tb i) tb (Array.range i)

@[inline, expose] def relKey (c : Nat) (C : Table) (v : Nat) : Nat :=
  if v == c then 2 else if ap C v == v then 1 else 0

@[inline, expose] def candAt (F : Table) (cs : Array Table) (b v : Nat) : Bool :=
  allIn 0 F.size fun k => relKey (ap F k) cs[k]! v == relKey (ap F k) cs[k]! b

@[expose] def candCount (O : COrbit) (tb : Array Table) (i : Nat) : Nat :=
  let F := (closTree tb i).pts
  let cs := F.map fun c => tabOf O c.toNat
  (List.range 3510).countP fun v => candAt F cs nfpBase[i]! v

@[expose] def reconTab (T : Tree) (tc : Array Table) (c0 : Nat) : Table := Id.run do
  let m := T.pts.size
  let mut im : Array Nat := Array.replicate m 0
  im := im.set! 0 c0
  for k in [1:m] do
    im := im.set! k (ap tc[ap T.lab k]! im[ap T.par k]!)
  let mut U : Table := Array.replicate 3510 0
  for k in [0:m] do
    U := U.set! (ap T.pts k) (UInt32.ofNat im[k]!)
  return U

@[inline, expose] def invFix (f : Nat → Nat) : Bool :=
  !allIn 0 3510 (fun i => f (f i) == i) || !allIn 0 3510 (fun i => f i != i)

@[expose] def leafNfp (A B U : Table) : Bool :=
  invFix (fun i => ap A (ap B i)) && !allIn 0 3510 (fun i => ap A (ap B (ap U i)) == i) &&
    invFix (fun i => ap A (ap B (ap U i)))

@[expose] def nfpChecks (O : COrbit) (chunks : Nat) : Bool :=
  let LJ := chainLetters O
  let L := sylLetters LJ
  let T := chainTrees 3510 L sylBase
  let t0 := treeTabs 3510 T[0]! L
  let t1 := treeTabs 3510 T[1]! L
  let tb := nfpBase.map (tabOf O)
  let tc := uImg.map (tabOf O)
  let F := closTree tb 6
  let U := reconTab F tc uImg[0]!
  (allIn 1 7 fun i => closOK tb i) && F.pts.size == 3510 &&
    (allIn 1 6 fun i => candCount O tb i == nfpBounds[i]!) &&
    (allIn 0 3510 fun i => ap U i < 3510) && invoOK 3510 U &&
    (allIn 0 6 fun j => ap U nfpBase[j]! == uImg[j]!) &&
    (allIn 0 6 fun j => compT 3510 U (compT 3510 tb[j]! U) == tc[j]!) &&
    (allIn 0 sylWords.size fun j =>
      sift T L sylQb chainQ 0 (apT (compT 3510 U (compT 3510 L[2 * j]! U)) chainQ)) &&
    parAll t0.size chunks fun k => t1.all fun B => leafNfp t0[k]! B U

@[expose] def nfpCertificate (chunks : Nat) : Bool := nfpChecks (orbitData ()) chunks

end CFSG.Sporadic.Fi22.Native
