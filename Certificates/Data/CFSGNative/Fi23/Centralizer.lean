module

public import Certificates.Data.CFSGNative.Fi23.Certificate
public import Certificates.Data.CFSGNative.Fi23.CentralizerData
public import Certificates.Data.CFSGNative.Fi22.Certificate

public section

namespace CFSG.Sporadic.Fi23.Native

open CFSG.Sporadic.Th.Native

set_option compiler.extract_closed false

@[expose] def dWordTable (O : WOrbit) : Table :=
  dWord.foldr (fun x T => compT 31671 (if x = 0 then O.alpha else O.beta) T) (idT 31671)

@[expose] def dTable (O : WOrbit) : Table := powT 31671 7 (dWordTable O)

@[expose] def treeAct (par lab al be D bi : Table) (k m : Nat) : Nat :=
  if _h : 0 < k ∧ ap par k < k then
    if ap lab k == 1 then ap al (treeAct par lab al be D bi (ap par k) (ap al m))
    else ap be (treeAct par lab al be D bi (ap par k) (ap bi m))
  else ap D m
termination_by k
decreasing_by all_goals exact _h.2

@[expose] def treeActTab (O : WOrbit) (D bi : Table) (k : Nat) : Table :=
  Array.ofFn (n := 31671) fun m =>
    UInt32.ofNat (treeAct O.par O.lab O.alpha O.beta D bi k m.val)

@[expose] def starPts (D : Table) : Array Nat :=
  ((List.range 31671).filter fun k => k != 0 && ap D k == k).toArray

@[expose] def starPos (e : Array Nat) : Array Nat :=
  let l := e.toList
  Array.ofFn (n := 31671) fun k => l.idxOf k.val

@[expose] def starPhiPos (_ : Unit := ()) : Array Nat :=
  let l := starPhi.toList
  Array.ofFn (n := 3510) fun u => l.idxOf u.val

@[expose] def starWordTab (O : WOrbit) (D bi : Table) (w : List Nat) : Table :=
  w.foldr (fun k P => compT 31671 (treeActTab O D bi k) P) (idT 31671)

@[expose] def centChecks (O : WOrbit) (O22 : CFSG.F3.Native.COrbit) (chunks : Nat) : Bool :=
  let D := dTable O
  let bi := genTables O (-2)
  let bi22 := Fi22.Native.genTables O22 (-2)
  let e := starPts D
  let p := starPos e
  e.size == 3510 && starPhi.size == 3510 &&
    allIn 0 3510 (fun i => starPhi[i]! < 3510 && starPhiPos[starPhi[i]!]! == i) &&
    parAll 3510 chunks (fun i => allIn 0 3510 fun j =>
      starPhi[p[treeAct O.par O.lab O.alpha O.beta D bi e[i]! e[j]!]!]! ==
        treeAct O22.par O22.lab O22.alpha O22.beta O22.alpha bi22 starPhi[i]! starPhi[j]!) &&
    starWord.all (fun k => e.contains k) &&
    powT 31671 11 (starWordTab O D bi starWord) == D

@[expose] def centCertificate (chunks : Nat) : Bool :=
  centChecks (orbitData ()) (Fi22.Native.orbitData ()) chunks

end CFSG.Sporadic.Fi23.Native
