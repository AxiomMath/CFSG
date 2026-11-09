module

public import Certificates.Data.Kernel.OpsRenL
public import Certificates.Data.Kernel.LocalQT.SecF3

public section

namespace CFSG.KC.OpsLayF3

open CFSG.KC.LQT CFSG.KC.Ord CFSG.KC.OpsLayK CFSG.KS.F3L CFSG.F3.Native CFSG.SectionRank.Native

structure Ctx where
  d : Nat
  E : Nat
  I : V

@[expose] noncomputable def strictV {α : Type} (v : V) (k : V → α) : α :=
  strictT v.p fun p => strictT v.m fun m => k ⟨p, m⟩

@[expose] noncomputable def mulV (x : Ctx) (X Y : V) : V := mulLane x.d x.E X Y

@[expose] noncomputable def powV (x : Ctx) (f : Nat) : V → Nat → V :=
  Nat.rec (motive := fun _ => V → Nat → V) (fun _ _ => x.I)
    (fun _ ih X e =>
      Bool.rec (motive := fun _ => V)
        (Bool.rec (motive := fun _ => V)
          (strictV (mulV x X X) fun X2 =>
            strictV (ih X2 (Nat.div e 2)) fun Y =>
              Bool.rec (motive := fun _ => V) Y (mulV x X Y) (Nat.beq (Nat.mod e 2) 1))
          X (Nat.beq e 1))
        x.I (Nat.beq e 0)) f

@[expose] def getV (x : Ctx) (R : List V) (i : Nat) : V := R.getD i x.I

@[expose] noncomputable def stepV3 (x : Ctx) (R : List V) : Op → V
  | .mul i j _ => mulV x (getV x R i) (getV x R j)
  | .pow e i _ => powV x 17 (getV x R i) e

@[expose] noncomputable def runV (x : Ctx) (prog : List Op) : List V → (List V → Bool) → Bool :=
  List.rec (motive := fun _ => List V → (List V → Bool) → Bool) (fun R k => k R)
    (fun o _ ih R k => strictV (stepV3 x R o) fun v => ih (R.set (Op.tgt o) v) k) prog

@[expose] noncomputable def eqVL : List V → List V → Bool
  | [], [] => true
  | a :: as, b :: bs => eqV a b && eqVL as bs
  | _, _ => false

@[expose] noncomputable def ctxOf (c : Lay) (K : Nat) : Ctx :=
  ⟨c.d, spreadE c.d c.d, gath3 c.w K c.ONE⟩

@[expose] noncomputable def allValid (c : Lay) (S : List Nat) : Bool :=
  S.all (validM c.p (Nat.mul c.d c.S) c.L c.H)

@[expose] noncomputable def gL (c : Lay) (K : Nat) (S : List Nat) : List V := S.map (gath3 c.w K)

@[expose] noncomputable def chunkV3 (c : Lay) (K : Nat) (ch : RChunk) (S S' : List Nat) : Bool :=
  allValid c S && allValid c S' &&
    runV (ctxOf c K) (ch.2.1.map opOf) (gL c K (padR c S ch.1)) fun R =>
      eqVL (ch.2.2.map (getV (ctxOf c K) R)) (gL c K S')

@[expose] noncomputable def chunkL3 (c : Lay) (K : Nat) (prog : List Op) (k i : Nat)
    (R S : List Nat) : Bool :=
  allValid c R && allValid c S &&
    runV (ctxOf c K) ((prog.drop (i * k)).take k) (gL c K R) fun R' => eqVL R' (gL c K S)

end CFSG.KC.OpsLayF3

end
