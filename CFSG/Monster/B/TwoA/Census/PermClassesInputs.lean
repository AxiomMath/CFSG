module

public import CFSG.Monster.B.TwoA.Census.MonoData
public import CFSG.Monster.B.TwoA.Census.PermBFS
public import CFSG.Monster.CodeAut.Bridge
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.GroupAction.ConjAct
public meta import CFSG.Monster.B.TwoA.Census.PermCert
public meta import CFSG.Monster.B.TwoA.Census.PermBFS
public meta import CFSG.Monster.B.TwoA.Census.MonoData

public section

namespace CFSG.Monster.B.TwoA.Census

open CFSG.Monster.Code

@[expose] def sylowGens : Array (Array ℕ) := sylowGenArr.toArray
@[expose] def c1Gens : Array (Array ℕ) := centGenArr1.toArray
@[expose] def c2Gens : Array (Array ℕ) := centGenArr2.toArray
@[expose] def abGens : Array (Array ℕ) := centGenArr0.toArray

@[expose] def sylowCert : TreeCert := bfsCert amul sylowGens idArr 2000
@[expose] def cent1Cert : TreeCert := bfsCert amul c1Gens idArr 30000
@[expose] def cent2Cert : TreeCert := bfsCert amul c2Gens idArr 10000
@[expose] def orb1Cert : TreeCert := bfsCert aconj abGens (seedArr.getD 1 #[]) 20000
@[expose] def orb2Cert : TreeCert := bfsCert aconj abGens (seedArr.getD 2 #[]) 40000

@[expose] def invIdx (c : TreeCert) : List ℕ :=
  (List.range c.pts.size).filter fun i => amul c.pts[i]! c.pts[i]! == idArr && c.pts[i]! != idArr

@[expose] def keyIndex (c : TreeCert) : Std.HashMap ℕ ℕ :=
  (List.range c.pts.size).foldl (fun m i => m.insert (akey c.pts[i]!) i) ∅

@[expose] def invCovered : Bool :=
  (invIdx sylowCert).all fun i =>
    (match (keyIndex orb1Cert).get? (akey sylowCert.pts[i]!) with
      | some j => decide (j < orb1Cert.pts.size) && orb1Cert.pts[j]! == sylowCert.pts[i]!
      | none => false) ||
    (match (keyIndex orb2Cert).get? (akey sylowCert.pts[i]!) with
      | some j => decide (j < orb2Cert.pts.size) && orb2Cert.pts[j]! == sylowCert.pts[i]!
      | none => false)

end CFSG.Monster.B.TwoA.Census
