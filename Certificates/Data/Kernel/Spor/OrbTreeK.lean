module

public import Certificates.Data.Kernel.Spor.RawTree

public section

namespace CFSG.KS.OrbTree

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def treeK (m w wl wb : Nat) (PS : Nat → Nat) (ORD PAR GEN : Nat) : Bool :=
  bAnd(permOK m wl (mask wl) (m * wl) ORD (pinvS m wl (mask wl) ORD),
  bAnd(Nat.beq (pg wl (mask wl) ORD 0) 0,
  bAnd(Nat.beq (Nat.shiftRight PAR (m * wl)) 0, bAnd(Nat.beq (Nat.shiftRight GEN (m * wb)) 0,
  allN m (fun i => bIf(Nat.beq i 0, true,
    strictB (pg wl (mask wl) PAR i) (fun p => strictB (pg wb (mask wb) GEN i) (fun g =>
      bAnd(Nat.blt p i, bAnd(Nat.blt g 2,
        Nat.beq (pg w (mask w) (PS g) (pg wl (mask wl) ORD p)) (pg wl (mask wl) ORD i)))))))))))

@[expose] noncomputable def subK (m w wl wb kS k : Nat) (PS : Nat → Nat) (st : Nat → Nat)
    (LAB ORD TPAR TGEN : Nat) : Bool :=
  bAnd(permOK m wl (mask wl) (m * wl) ORD (pinvS m wl (mask wl) ORD),
  bAnd(Nat.beq (Nat.shiftRight LAB (m * wb)) 0, bAnd(Nat.beq (Nat.shiftRight TPAR (m * wl)) 0,
  bAnd(Nat.beq (Nat.shiftRight TGEN (m * wb)) 0,
  bAnd(allN m (fun p => Nat.blt (pg wb (mask wb) LAB p) k),
  bAnd(Nat.beq (st 0) 0, bAnd(Nat.beq (st k) m, bAnd(allN k (fun c => Nat.blt (st c) (st (Nat.succ c))),
  bAnd(Nat.beq (pg wb (mask wb) LAB 0) 0, bAnd(Nat.beq (pg wl (mask wl) ORD 0) 0,
  bAnd(allN k (fun c => allN (Nat.sub (st (Nat.succ c)) (st c)) (fun d =>
    strictB (Nat.add (st c) d) (fun i =>
    bAnd(Nat.beq (pg wb (mask wb) LAB (pg wl (mask wl) ORD i)) c, bIf(Nat.beq d 0, true,
      strictB (pg wl (mask wl) TPAR i) (fun tp => strictB (pg wb (mask wb) TGEN i) (fun tg =>
        bAnd(Nat.ble (st c) tp, bAnd(Nat.blt tp i, bAnd(Nat.blt tg kS,
        bAnd(Nat.beq (pg w (mask w) (PS tg) 0) 0,
          Nat.beq (pg w (mask w) (PS tg) (pg wl (mask wl) ORD tp)) (pg wl (mask wl) ORD i)))))))))))),
  allN kS (fun g => strictB (PS g) (fun P => bIf(Nat.beq (pg w (mask w) P 0) 0,
    allN m (fun p => Nat.beq (pg wb (mask wb) LAB (pg w (mask w) P p)) (pg wb (mask wb) LAB p)),
    true))))))))))))))

@[expose] noncomputable def orbitK (n m w wn : Nat) (NS PS : Nat → Nat) (O : Nat) : Bool :=
  bAnd(Nat.beq (Nat.shiftRight O (m * wn)) 0, bAnd(Nat.blt (pg wn (mask wn) O (Nat.sub m 1)) n,
  bAnd(allN (Nat.sub m 1) (fun j => Nat.blt (pg wn (mask wn) O j) (pg wn (mask wn) O (Nat.succ j))),
  allN m (fun j => allN 2 (fun i => strictB (pg w (mask w) (PS i) j) (fun j' =>
    bAnd(Nat.blt j' m, Nat.beq (pg wn (mask wn) (NS i) (pg wn (mask wn) O j))
      (pg wn (mask wn) O j'))))))))

end CFSG.KS.OrbTree

end
