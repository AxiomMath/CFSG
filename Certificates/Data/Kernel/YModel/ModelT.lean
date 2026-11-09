module

public import Certificates.Data.Kernel.YModel.Model

public section

namespace CFSG.KC.YModel

open CFSG.KC CFSG.KC.MonsterConv.Perm CFSG.KC.Loop

@[expose] noncomputable def tauOK (k w : Nat) (U TT NT : Nat → Nat) (Z a p : Nat) : Bool :=
  andB (netOK k (NT a))
    (bIf(Nat.beq (ptL (TT a)) (nat_lit 0),
      Nat.beq (apK k (NT a) (idP k)) (idP k),
      (fun x => andB (Nat.blt p Z) (andB (Nat.beq (ptL (TT a)) (Nat.succ (ptL (TT p))))
        (andB (Nat.beq (ptP (TT a)) (catW w x (nat_lit 1) (ptP (TT p))))
          (Nat.beq (apK k (NT a) (idP k)) (apK k (NT p) (apK k (codeNet k U x) (idP k)))))))
      (Nat.land (ptP (TT a)) (Nat.sub (Nat.shiftLeft (nat_lit 1) w) (nat_lit 1)))))

@[expose] noncomputable def tausOK (k w : Nat) (U TT NT : Nat → Nat) (Z a0 : Nat) (ps : List Nat) :
    Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun p _ ih a => andB (tauOK k w U TT NT Z a p) (strictB (Nat.succ a) ih)) ps a0

@[expose] noncomputable def recT (k w : Nat) (U TT NT : Nat → Nat) (Z hi top a j rec : Nat) : Bool :=
  (fun ty ta => andB (Nat.blt (ptX rec) Z)
    (bIf(Nat.beq (ptL rec) (nat_lit 65535),
      andB (Nat.beq (ptP ty) (catW w (Nat.mul (nat_lit 2) (Nat.succ j)) (nat_lit 1) (ptP ta)))
        (Nat.beq (ptL ty) (Nat.succ (ptL ta))),
      andB (codesIn w hi top (ptP rec) (ptL rec))
        (Nat.beq (apK k (NT a) (apK k (U j) (idP k)))
          (netsApply k (wid k) (repU (wid k) k) (wordNets k w U (ptP rec) (ptL rec))
            (apK k (NT (ptX rec)) (idP k)))))))
    (TT (ptX rec)) (TT a)

@[expose] noncomputable def schT (k w : Nat) (U TT NT : Nat → Nat) (Z lo hi top a0 cnt : Nat)
    (recs : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool)
    (fun r => Nat.beq r (Nat.mul cnt (Nat.sub hi lo)))
    (fun rec _ ih r => andB (Nat.blt r (Nat.mul cnt (Nat.sub hi lo)))
      (andB (recT k w U TT NT Z hi top (Nat.add a0 (Nat.div r (Nat.sub hi lo)))
          (Nat.add lo (Nat.mod r (Nat.sub hi lo))) rec)
        (strictB (Nat.succ r) ih)))
    recs (nat_lit 0)

end CFSG.KC.YModel

end
