module

public import CFSG.Certificates.Kernel.Enum.Defs
public import Certificates.Data.Kernel.DecText
public import Certificates.Data.Kernel.EvenSporM22.M22StdDefs

public section

namespace CFSG.KC.I22F

open CFSG.KC.Enum CFSG.KC.LQT.Cov CFSG.KC.LQT.Syl CFSG.KC.M22S

@[expose] noncomputable def chkL (P : Nat) (l : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun i => Nat.beq i (nat_lit 32256))
    (fun x _ ih i => bAnd(Nat.beq x (pg (nat_lit 15) (nat_lit 32767) P i), ih (Nat.succ i))) l

@[expose] noncomputable def lsel (A AI B BI : Nat) (l : Nat × Bool) : Nat :=
  Prod.rec (motive := fun _ => Nat) (fun g s => nIf(Nat.beq g (nat_lit 0),
    Bool.rec (motive := fun _ => Nat) AI A s, Bool.rec (motive := fun _ => Nat) BI B s)) l

@[expose] noncomputable def wimg (A AI B BI : Nat) (v : List (Nat × Bool)) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun p => p)
    (fun l _ ih p => pg (nat_lit 15) (nat_lit 32767) (lsel A AI B BI l) (ih p)) v

@[expose] noncomputable def fixW (A AI B BI : Nat) (v : List (Nat × Bool)) : Bool :=
  allN (nat_lit 32256) (fun i => Nat.beq (wimg A AI B BI v i) i)

@[expose] noncomputable def tabW (A AI B BI : Nat) (v : List (Nat × Bool)) (R : Nat) : Bool :=
  allN (nat_lit 32256) (fun i => Nat.beq (wimg A AI B BI v i) (pg (nat_lit 15) (nat_lit 32767) R i))

@[expose] noncomputable def commW (P Q : Nat) : Bool :=
  eq22 (nat_lit 32256) (nat_lit 15) (nat_lit 32767) P Q Q P

@[expose] noncomputable def xpt (A AI B BI : Nat) (sA sB : List (Nat × Bool)) (xw : List (List Nat))
    (i : Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun p => p)
    (fun l _ ih p => strictN (ih p) (fun q => nIf(Nat.beq l (nat_lit 0), wimg A AI B BI sA q,
      wimg A AI B BI sB q))) (getK xw i [])

@[expose] noncomputable def vpt (A AI B BI : Nat) (sA sB : List (Nat × Bool)) (xw : List (List Nat))
    (wd : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun p => p)
    (fun l _ ih p => strictN (ih p) (xpt A AI B BI sA sB xw (Nat.mod l (nat_lit 3)))) wd

@[expose] noncomputable def witOK (A AI B BI : Nat) (sA sB : List (Nat × Bool)) (xw : List (List Nat))
    (u v : List Nat) (p : Nat) : Bool :=
  bAnd(Nat.blt p (nat_lit 32256),
    Bool.rec (motive := fun _ => Bool) true false
      (Nat.beq (vpt A AI B BI sA sB xw u (vpt A AI B BI sA sB xw v p))
        (vpt A AI B BI sA sB xw v (vpt A AI B BI sA sB xw u p))))

@[expose] noncomputable def witsD (A AI B BI : Nat) (sA sB : List (Nat × Bool)) (D : CD)
    (wl : List (Nat × Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun r _ ih =>
    bAnd(Nat.blt r.1 D.nV, bAnd(Nat.blt r.2.1 D.nV,
      bAnd(witOK A AI B BI sA sB D.xw (getK D.words r.1 []) (getK D.words r.2.1 []) r.2.2, ih)))) wl

@[expose] noncomputable def witsK (A AI B BI : Nat) (sA sB : List (Nat × Bool)) (cs : List Char)
    (wl : List (Nat × Nat × Nat)) : Bool :=
  Option.rec (motive := fun _ => Bool) false (fun D => witsD A AI B BI sA sB D wl) (parseCov cs)

@[expose] noncomputable def recK (wl : List (Nat × Nat × Nat)) (v w : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun r _ ih => bIf(bAnd(Nat.beq r.1 v, Nat.beq r.2.1 w), true, ih)) wl

@[expose] noncomputable def isInvK (e : Nat) : Bool :=
  bAnd(Bool.rec (motive := fun _ => Bool) true false (Nat.beq e (CFSG.KC.LQT.P.one 22)),
    Nat.beq (CFSG.KC.LQT.P.mul 22 e e) (CFSG.KC.LQT.P.one 22))

@[expose] noncomputable def candK (E : List Nat) (wl : List (Nat × Nat × Nat)) (v w : Nat) : Bool :=
  bAnd(Bool.rec (motive := fun _ => Bool) true false (Nat.beq w v),
    bAnd(Nat.beq (CFSG.KC.LQT.P.mul 22 (getK E v 0) (getK E w 0))
        (CFSG.KC.LQT.P.mul 22 (getK E w 0) (getK E v 0)),
      Bool.rec (motive := fun _ => Bool) true false (recK wl v w)))

@[expose] noncomputable def cntD (E : List Nat) (wl : List (Nat × Nat × Nat)) (nV : Nat) : Bool :=
  (fun invs => Nat.ble (lenK (List.filter (fun v => Nat.ble 14 (lenK (List.filter (candK E wl v)
    invs))) invs)) 14) (List.filter (fun v => isInvK (getK E v 0)) (List.range nV))

@[expose] noncomputable def cntK (cA cB : Nat) (cs : List Char) (wl : List (Nat × Nat × Nat)) : Bool :=
  Option.rec (motive := fun _ => Bool) false (fun D => cntD (eltsOf cA cB D) wl D.nV) (parseCov cs)

@[expose] def lA : Nat × Bool := (0, true)

@[expose] def lAi : Nat × Bool := (0, false)

@[expose] def lB : Nat × Bool := (1, true)

@[expose] def lBi : Nat × Bool := (1, false)

@[expose] def sAK : List (Nat × Bool) :=
  [lA, lB, lB, lA, lA, lBi, lBi, lAi, lBi, lBi, lA, lB, lB, lA, lB, lAi]

@[expose] def sBK : List (Nat × Bool) :=
  [lB, lB, lA, lBi, lBi, lA, lA, lB, lB, lB, lA, lBi, lA, lB]

@[expose] def relK : List (List (Nat × Bool)) :=
  [[lA, lA, lA, lA, lB, lAi, lB, lAi, lB], [lA, lA, lB, lAi, lBi, lA, lB, lB, lAi, lBi],
    [lB, lB, lB, lB, lB, lB, lB, lB, lB, lB, lB], [lA, lA, lA, lA, lA],
    [lA, lBi, lA, lBi, lA, lBi], [lA, lB, lB, lA, lB, lB, lA, lB, lB, lA, lB, lB, lA, lB, lB]]

@[expose] def cwA : List (Nat × Bool) :=
  [lAi, lBi, lAi, lB, lAi, lBi, lA, lB, lA, lA, lB, lA, lA, lBi, lBi, lAi, lB, lAi, lAi]

@[expose] def cwB : List (Nat × Bool) :=
  [lBi, lA, lBi, lBi, lAi, lAi, lBi, lAi, lB, lB, lB, lAi, lBi, lA, lB, lA, lA]

end CFSG.KC.I22F

end
