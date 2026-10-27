module

public import Certificates.Data.Kernel.Census.PackedExc

public section

namespace CFSG.KC.Census

open CFSG.KC.Enum

@[expose] noncomputable def strictLA {β : Sort _} (l : List Nat) (k : List Nat → β) : β :=
  List.rec (motive := fun _ => (List Nat → β) → β) (fun k => k [])
    (fun a _ ih k => Nat.rec (motive := fun _ => β) (ih fun t => k (nat_lit 0 :: t))
      (fun m _ => ih fun t => k (Nat.succ m :: t)) a) l k

@[expose] noncomputable def strictNA {β : Sort _} (y : Nat) (k : Nat → β) : β :=
  Nat.rec (motive := fun _ => β) (k (nat_lit 0)) (fun m _ => k (Nat.succ m)) y

@[expose] def strictLBo {β : Sort _} (l : List Bool) (k : List Bool → β) : β :=
  List.rec (motive := fun _ => (List Bool → β) → β) (fun k => k [])
    (fun a _ ih k => Bool.rec (motive := fun _ => β) (ih fun t => k (false :: t))
      (ih fun t => k (true :: t)) a) l k

@[expose] def walkF (f : Nat → Nat → Bool) : List Nat → List Bool → List Nat → Bool
  | [], _, _ => true
  | u :: us, b :: bs, c :: cs => (!b || f u c) && walkF f us bs cs
  | u :: us, b :: bs, [] => (!b || f u 0) && walkF f us bs []
  | _ :: _, [], _ => false

section Checks

variable (n w : Nat)

@[expose] noncomputable def pspanL : List Nat → List Nat
  | [] => [pid n w]
  | b :: bs => strictLA (pspanL bs) fun s => s.flatMap fun x => [x, pc n w b x]

@[expose] noncomputable def pinvFl (cS : ArrCertP) : List Bool :=
  strictNA (pid n w) fun e => cS.pts.toList.map fun u => Nat.beq (pc n w u u) e

@[expose] noncomputable def withFl (cS : ArrCertP) (k : List Bool → Bool) : Bool :=
  strictLBo (pinvFl n w cS) k

@[expose] noncomputable def pchildAt (bi ci : List Nat) (u : Nat) (bj : List Nat) : Bool :=
  (bj.all fun b => ci.any (Nat.beq b) || ci.any (Nat.beq (pc n w u b))) &&
    strictLA (pspanL n w bj) fun cj => (bi.all fun b => cj.any (Nat.beq b)) && cj.any (Nat.beq u)

@[expose] noncomputable def pchildL (nl : List NodeP) (sz : Nat) (bi ci : List Nat) (u j : Nat) :
    Bool :=
  Nat.blt j sz && (match nl.getD j default with | ⟨bj, _, _⟩ => pchildAt n w bi ci u bj.toList)

@[expose] noncomputable def pwalkF (nl : List NodeP) (sz : Nat) (bi ci : List Nat)
    (pts : List Nat) (fl : List Bool) (ch : List Nat) : Bool :=
  walkF (fun u c => !(bi.all fun b => pcommA n w u b) || ci.any (Nat.beq u) ||
    pchildL n w nl sz bi ci u c) pts fl ch

@[expose] noncomputable def pnodeAtL (ps : List Nat) (wk : ArrCertP → Bool) (cS : ArrCertP)
    (fl : List Bool) (nl : List NodeP) (sz : Nat) (basis : Array Nat) (wit : WitP)
    (ch : Array Nat) : Bool :=
  strictLA (pspanL n w basis.toList) fun ci =>
    let cE : ArrCertP := ⟨Array.mk ci, (pmaskCert n w basis).edges, (pmaskCert n w basis).par,
      (pmaskCert n w basis).lab⟩
    penumOK n w basis ps cE && wk cE &&
      (wit.isMono || pwalkF n w nl sz basis.toList ci cS.pts.toList fl ch.toList)

@[expose] noncomputable def pnodeL (ps : List Nat) (inX outX : Nat → Bool)
    (allowPW allowInX allowU : Bool) (cS : ArrCertP) (nodes : Array NodeP)
    (wcs : Array (Array ArrCertP)) (fl : List Bool) (i : Nat) : Bool :=
  strictB nodes.size fun sz => match nodes.toList.getD i default with
    | ⟨b, wt, ch⟩ => pnodeAtL n w ps
        (fun cE => pwitOK n w ps inX outX allowPW allowInX allowU b cE (wcs.toList.getD i default)
          wt) cS fl nodes.toList sz b wt ch

@[expose] noncomputable def pnodeL2 (ps : List Nat) (inX outX : Nat → Bool)
    (allowPW allowInX allowU : Bool) (cS : ArrCertP) (nodes : Array NodeP)
    (wcs : Array (Array ArrCertP)) (pfs : Array PerfWP) (fl : List Bool) (i : Nat) : Bool :=
  strictB nodes.size fun sz => match nodes.toList.getD i default with
    | ⟨b, wt, ch⟩ => pnodeAtL n w ps
        (fun cE => pwitOK2 n w ps inX outX allowPW allowInX allowU b cE (wcs.toList.getD i default)
          (pfs.toList.getD i default) wt) cS fl nodes.toList sz b wt ch

@[expose] noncomputable def pexcAtL (ps : List Nat) (inW : Nat → Bool) (cS : ArrCertP)
    (nodes : Array NodeP) (cN : Array ArrCertP) (e0 : Array Nat) (excs : List ExcRefP)
    (fl : List Bool) (i : Nat) : Bool :=
  strictB nodes.size fun sz => match nodes.toList.getD i default with
    | ⟨b, _, ch⟩ => strictLA (pspanL n w b.toList) fun ci =>
      penumOK n w b ps ⟨Array.mk ci, (pmaskCert n w b).edges, (pmaskCert n w b).par,
          (pmaskCert n w b).lab⟩ && pexcOK n w ps inW e0 cN excs i &&
        pwalkF n w nodes.toList sz b.toList ci cS.pts.toList fl ch.toList

@[expose] noncomputable def pnodeExcL (ps : List Nat) (inX outX inW : Nat → Bool)
    (allowPW allowInX allowU : Bool) (cS : ArrCertP) (nodes : Array NodeP)
    (cN : Array ArrCertP) (wcs : Array (Array ArrCertP)) (e0 : Array Nat) (excs : List ExcRefP)
    (fl : List Bool) (i : Nat) : Bool :=
  pnodeL n w ps inX outX allowPW allowInX allowU cS nodes wcs fl i ||
    pexcAtL n w ps inW cS nodes cN e0 excs fl i

end Checks

end CFSG.KC.Census
