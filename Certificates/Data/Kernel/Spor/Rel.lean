module

public import Certificates.Data.Kernel.Spor.Mathieu
public import Certificates.Data.CFSGNative.Bridge.SurjA

public section

namespace CFSG.KS.Rel

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu

@[expose] noncomputable def letter (A Ai B Bi : Nat) (l : Nat × Bool) : Nat :=
  Prod.rec (motive := fun _ => Nat)
    (fun i b => nIf(Nat.beq i (nat_lit 0), nIf(b, A, Ai), nIf(b, B, Bi))) l

@[expose] noncomputable def wordP (n w m idn A Ai B Bi : Nat) (v : List (Nat × Bool)) : Nat :=
  List.rec (motive := fun _ => Nat) idn
    (fun l _ ih => strictN ih (fun T => pcomp n w m (letter A Ai B Bi l) T)) v

@[expose] noncomputable def relsId (n w m idn A Ai B Bi : Nat) (rels : List (List (Nat × Bool))) :
    Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun v _ ih => bAnd(Nat.beq (wordP n w m idn A Ai B Bi v) idn, ih)) rels

@[expose] noncomputable def tabOK (n : Nat) (t : Array UInt32) : Bool :=
  bAnd(Nat.beq (lenU t.toList) n, allLtU n t.toList)

@[expose] noncomputable def relK (n w : Nat) (α αi β βi : Array UInt32)
    (rels : List (List (Nat × Bool))) : Bool :=
  strictB (mask w) (fun m =>
  bAnd(Nat.blt n (nat_lit 16777216), bAnd(Nat.blt (Nat.succ n) m,
  bAnd(tabOK n α, bAnd(tabOK n αi, bAnd(tabOK n β, bAnd(tabOK n βi,
  strictB (pidn n w) (fun idn =>
  strictB (packU w α.toList) (fun A => strictB (packU w αi.toList) (fun Ai =>
  strictB (packU w β.toList) (fun B => strictB (packU w βi.toList) (fun Bi =>
    relsId n w m idn A Ai B Bi rels))))))))))))

end CFSG.KS.Rel

end
