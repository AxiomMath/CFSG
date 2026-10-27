module

public import Certificates.Data.A6EOne

public section

namespace CFSG.Quasithin.H13.A6EOne

open CFSG.QuasithinUnique.A6Facts.Core

@[expose] noncomputable def decK (k : Nat) : Nat → List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun _ ih x => Nat.mod x 16 :: ih (Nat.div x 16)) k

@[expose] noncomputable def dec (x : Nat) : List Nat := decK 10 x

@[expose] noncomputable def encL (c : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun a _ ih => Nat.add a (Nat.mul 16 ih)) c

@[expose] noncomputable def laneN (x j : Nat) : Nat :=
  bif Nat.blt j 10 then Nat.mod (Nat.shiftRight x (Nat.mul 4 j)) 16 else 0

@[expose] noncomputable def mulN (x y : Nat) : Nat := encL ((dec y).map (laneN x))

@[expose] noncomputable def invN (x : Nat) : Nat :=
  encL (CFSG.QuasithinUnique.Setup.X3Aut.invC (dec x))

@[expose] noncomputable def eqN (x y : Nat) : Bool :=
  Nat.beq (Nat.mod x 1099511627776) (Nat.mod y 1099511627776)

@[expose] noncomputable def memN (L : List Nat) (x : Nat) : Bool := L.any fun a => eqN x a

@[expose] noncomputable def cidN : Nat := encL cid

@[expose] noncomputable def DofT (T : Nat → Nat) (n : Nat) : Nat :=
  bif Nat.blt n 1440 then T n else cidN

@[expose] noncomputable def pslN : List Nat := pslLit.map encL

@[expose] noncomputable def repsInvN : List Nat := autRepsInv.map encL

@[expose] noncomputable def conjN (x e : Nat) : Nat := mulN (mulN x e) (invN x)

@[expose] noncomputable def commN (x y : Nat) : Nat := mulN (mulN (mulN x y) (invN x)) (invN y)

@[expose] noncomputable def inXN (I : List Nat) (c : Nat) : Bool :=
  I.any fun i => memN pslN (mulN c (repsInvN.getD i cidN))

@[expose] noncomputable def isSubN (L : List Nat) : Bool :=
  memN L cidN && L.all (fun a => L.all fun b => memN L (mulN a b)) && L.all fun a => memN L (invN a)

@[expose] noncomputable def commAllN (c : Nat) (E : List Nat) : Bool :=
  E.all fun e => eqN (mulN c e) (mulN e c)

section Checks

variable (g : Grp) (D : Nat → Nat)

@[expose] noncomputable def Grp.ScN : List Nat := g.S.map D

@[expose] noncomputable def Grp.EcN (j : Nat) : List Nat := (g.inv.getD j []).map D

@[expose] noncomputable def Grp.chkWN (w : Wit) : Bool :=
  let Kc := w.K.map D
  let Qc := w.Q.map D
  let Pc := w.P.map D
  let Ac := g.EcN D w.A
  let sk := ((g.ScN D).filter (memN Kc)).length
  decide (w.A < g.inv.length) && decide (g.cls.getD w.A 0 < g.m) &&
    isSubN Kc && isSubN Qc && isSubN Pc && decide (Kc.map dec).Nodup &&
    decide (Qc.map dec).Nodup && decide (Pc.map dec).Nodup &&
    Kc.all (inXN g.I) && Ac.all (memN Kc) &&
    (g.ScN D).all (fun s => !commAllN s Ac || memN Kc s) &&
    decide (0 < sk) && Kc.length % sk == 0 && (Kc.length / sk) % 2 == 1 &&
    Qc.all (memN (g.ScN D)) && Qc.all (memN Kc) &&
    Kc.all (fun k => Qc.all fun q => memN Qc (conjN k q)) &&
    (g.ScN D).all (fun s => !memN Kc s || memN Qc s ||
      Kc.any fun k => !memN (g.ScN D) (conjN (invN k) s)) &&
    Qc.all (memN Pc) && Pc.all (memN Kc) &&
    Kc.all (fun k => Pc.all fun x => memN Pc (conjN k x)) &&
    (w.p == 3 || w.p == 5) && Pc.length == Qc.length * w.p &&
    Kc.length % Pc.length == 0 && isPow2 (Kc.length / Pc.length) &&
    Ac.length == 2 * (Ac.filter (memN Qc)).length &&
    (g.ScN D).all (fun s => !memN Kc s || Ac.all fun a => memN Qc (commN s a)) &&
    Pc.any fun x => Ac.any fun a => !memN Qc (commN x a)

@[expose] noncomputable def Grp.chkWitN : Bool := g.wit.all (g.chkWN D)

end Checks

end CFSG.Quasithin.H13.A6EOne

end
