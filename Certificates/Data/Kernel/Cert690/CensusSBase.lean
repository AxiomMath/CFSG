module

public import Certificates.Data.Kernel.Cert690.CensusS
public import Certificates.Data.Kernel.Cert690.CBase

public section

namespace CFSG.KC.C690S

open CFSG.KC.C690 CFSG.KC.Enum

@[expose] noncomputable def inOS (G : GK) (c : Nat) : Bool :=
  (fun i => bAnd(Nat.blt i G.n, Nat.beq (G.getO i) c)) (G.ix c)

@[expose] noncomputable def subProds (l : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun W => W)
    (fun x _ ih W => ih (List.append W (List.map (fun w => mulF w x) W))) l [oneF]

@[expose] noncomputable def stabD (G : GK) (B : SBase) (k c a : Nat) : Bool :=
  bAnd(bAnd(Nat.beq a B.b, inOS G c),
    bIf(Nat.blt (Nat.succ k) B.nS, strictB (fS B.spk (Nat.succ k)) (Nat.blt c), true))

@[expose] noncomputable def stabC (G : GK) (B : SBase) (k c : Nat) : Bool :=
  strictB (actS c B.b) (stabD G B k c)

@[expose] noncomputable def stabS (G : GK) (B : SBase) : Bool :=
  allS (fun k => strictB (fS B.spk k) (stabC G B k)) (List.range B.nS)

@[expose] noncomputable def fcS (LC : List (List Nat)) : List Nat → List (List Nat) → Nat → Bool :=
  List.rec (motive := fun _ => List (List Nat) → Nat → Bool)
    (fun fg n => List.rec (motive := fun _ => Bool) (Nat.beq n (lenS LC)) (fun _ _ _ => false) fg)
    (fun c _ ih fg n => List.rec (motive := fun _ => Bool) false
      (fun gs fg' _ => bIf(Nat.beq (Nat.succ c) n, ih fg' n,
        bAnd(Nat.beq c n, bAnd(allS (fun x => memS x (nthS [] LC c)) gs, ih fg' (Nat.succ n)))))
      fg)

@[expose] noncomputable def baseS (G : GK) (Llist : Array (Array Nat)) (cs : List Nat)
    (B : SBase) : Bool :=
  bAnd(stabS G B,
  bAnd(allS (fun p => (fun t => bAnd(inOS G t, bAnd(Nat.beq (actS t B.b) p,
      Nat.beq (mulF t (nthS (nat_lit 0) B.tpI p)) oneF))) (nthS (nat_lit 0) B.tpT p)) B.sing,
  bAnd(allS (allS (inOS G)) B.fg,
  bAnd(allS (inOS G) B.pglc,
  bAnd(Nat.beq (lenS B.fc) B.nF,
  bAnd(Nat.beq (lenS B.LG) (lenS B.LC),
  bAnd(Nat.beq (lenS cs) (lenS B.LC),
  bAnd(fcS B.LC B.fc B.fg (nat_lit 0),
    zipS (fun c p => bAnd(allS (fun x => memS x p.2) p.1,
        bAnd(allS (fun x => memS x (subProds p.1)) p.2,
          zipS (fun x i => Nat.beq x (G.getO i)) p.2 (Llist[c]!).toList)))
      cs (List.zip B.LG B.LC)))))))))

end CFSG.KC.C690S

end
