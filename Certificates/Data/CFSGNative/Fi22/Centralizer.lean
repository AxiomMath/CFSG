module

public import Certificates.Data.CFSGNative.Fi22.Local

public section

namespace CFSG.Sporadic.Fi22.Native

open CFSG.F3.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.F4.Native

set_option compiler.extract_closed false

@[expose] def cTab (O : COrbit) (bi : Table) (k : Nat) : Table :=
  if _h : 0 < k ∧ ap O.par k < k then
    if ap O.lab k == 1 then compT 3510 (compT 3510 O.alpha (cTab O bi (ap O.par k))) O.alpha
    else compT 3510 (compT 3510 O.beta (cTab O bi (ap O.par k))) bi
  else O.alpha
termination_by k
decreasing_by all_goals exact _h.2

@[expose] def ePos (e : Array Nat) : Array Nat :=
  Array.ofFn (n := 3510) fun k => e.toList.idxOf k.val

@[expose] def phiPos (_ : Unit := ()) : Array Nat := Array.ofFn (n := 693) fun u => phiData.toList.idxOf u.val

@[expose] def rrImg (e p : Array Nat) (L : Table) : Array Nat :=
  Array.ofFn (n := 693) fun u => phiData[p[ap L e[phiPos[u.val]!]!]!]!

@[expose] def aWord (_ : Unit := ()) : List Nat := [3468, 3243, 2605, 168, 1897]

@[expose] def aWord2 (_ : Unit := ()) : List Nat := [889, 1897, 2614, 929, 3173, 762]

@[expose] def wordTab (O : COrbit) (bi : Table) (w : List Nat) : Table :=
  w.foldr (fun k P => compT 3510 (cTab O bi k) P) (idT 3510)

@[expose] def centChecks (O : COrbit) : Bool :=
  let e := eaPts O
  let p := ePos e
  let bi := genTables O (-2)
  let L := chainLetters O
  e.size == 693 && phiData.size == 693 &&
    allIn 0 693 (fun i => phiData[i]! < 693 && phiPos[phiData[i]!]! == i) &&
    (levelLetters L chainBase 1).all (fun l =>
      allIn 0 693 (fun i => p[ap L[l]! e[i]!]! < 693) &&
        sift t46Trees t46Letters t46Base t46Q 0 (rrImg e p L[l]!)) &&
    allIn 0 693 (fun i =>
      let T := cTab O bi e[i]!
      let tv := tvTable uPts[phiData[i]!]!
      allIn 0 693 fun j => phiData[p[ap T e[j]!]!]! == ap tv phiData[j]!) &&
    aWord.all (fun k => e.contains k) &&
    powT 3510 9 (wordTab O bi aWord) == O.alpha &&
    aWord2.all (fun k => e.contains k) &&
    powT 3510 11 (wordTab O bi aWord2) == O.alpha

@[expose] def centCertificate (_ : Unit) : Bool := centChecks (orbitData ())

end CFSG.Sporadic.Fi22.Native
