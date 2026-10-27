module

public import Certificates.Data.Kernel.SporSch.TitsInv

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def popc (T M : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.add acc (Nat.land (Nat.shiftRight M i) (nat_lit 1))) T

@[expose] noncomputable def gptC (LR TR : Nat → Nat) (k i : Nat) : Nat :=
  strictN (rcnt (LR 1)) (fun c1 => strictN (rcnt (LR 2)) (fun c2 =>
  strictN (rcnt (LR 3)) (fun c3 => strictN (rcnt (LR 4)) (fun c4 =>
  strictN (Nat.div k c4) (fun k3 => strictN (Nat.div k3 c3) (fun k2 =>
  strictN (Nat.div k2 c2) (fun k1 => strictN (Nat.div k1 c1) (fun a =>
  gptR (trAt 1755 (1755 * 11) LR TR 0 a) (trAt 1755 (1755 * 11) LR TR 1 (Nat.mod k1 c1))
    (trAt 1755 (1755 * 11) LR TR 2 (Nat.mod k2 c2)) (trAt 1755 (1755 * 11) LR TR 3 (Nat.mod k3 c3))
    (trAt 1755 (1755 * 11) LR TR 4 (Nat.mod k c4)) i))))))))

@[expose] noncomputable def baseComm (BP nb : Nat) (gx gy : Nat → Nat) : Bool :=
  allN nb (fun t => strictB (pg 11 (mask 11) BP t) (fun b => Nat.beq (gx (gy b)) (gy (gx b))))

@[expose] noncomputable def ctK (BP : Nat) (LR TR : Nat → Nat) (CK : List Nat)
    (t0 t1 t2 t3 t4 : Nat) : Bool :=
  allL (fun k => baseComm BP 5 (gptR t0 t1 t2 t3 t4) (gptC LR TR k)) CK

@[expose] noncomputable def siftPfB (LR TRI : Nat → Nat) (BP NBP : Nat) (f : Nat) :
    Nat → (Nat → Nat) → Bool :=
  Nat.rec (motive := fun _ => Nat → (Nat → Nat) → Bool)
    (fun _ g => allN 5 (fun t => strictB (pg 11 (mask 11) NBP t) (fun b => Nat.beq (g b) b)))
    (fun _ ih l g => strictB (LR l) (fun R =>
      strictB (rpos 11 (mask 11) (1755 * 11) R (g (pg 11 (mask 11) BP l))) (fun k =>
      bIf(Nat.blt k (rcnt R),
        strictB (TRI (Nat.add (roff 1755 (1755 * 11) R) k)) (fun t =>
          ih (Nat.succ l) (fun i => pgR t (g i))),
        false))))
    f

@[expose] noncomputable def ktKB (LR TRI : Nat → Nat) (BP NBP t0 t1 t2 t3 t4 : Nat) : Bool :=
  siftPfB LR TRI BP NBP 5 0 (gptR t0 t1 t2 t3 t4)

@[expose] noncomputable def treeStep (BP : Nat) (LR TR : Nat → Nat) (c g p : Nat) : Bool :=
  allN 5 (fun t => strictB (pg 11 (mask 11) BP t) (fun b =>
    Nat.beq (gptC LR TR c b) (gptC LR TR g (gptC LR TR p b))))

@[expose] noncomputable def genTreeK (BP : Nat) (LR TR : Nat → Nat) (G : List Nat) :
    List Nat → List (Nat × Nat) → List Nat → Bool :=
  fun C => List.rec (motive := fun _ => List (Nat × Nat) → List Nat → Bool)
    (fun W _ => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) W)
    (fun c _ ih W S => List.rec (motive := fun _ => Bool) false
      (fun gp W' _ => Prod.rec (motive := fun _ => Bool) (fun g p =>
        bAnd(memN g G, bAnd(memN p S, bAnd(treeStep BP LR TR c g p, ih W' (c :: S))))) gp) W) C

@[expose] noncomputable def qtreeK (BP : Nat) (LR TR : Nat → Nat) (G Q : List Nat)
    (W : List (Nat × Nat)) : Bool :=
  bAnd(allL (fun g => memN g Q) G,
    List.rec (motive := fun _ => Bool) false
      (fun c Q' _ => bAnd(Nat.beq c 0, genTreeK BP LR TR G Q' W [c])) Q)

@[expose] noncomputable def ctKG (BP : Nat) (LR TR : Nat → Nat) (G : List Nat)
    (t0 t1 t2 t3 t4 : Nat) : Bool :=
  allL (fun k => baseComm BP 5 (gptR t0 t1 t2 t3 t4) (gptC LR TR k)) G

@[expose] noncomputable def ktK (LR TRI : Nat → Nat) (BP t0 t1 t2 t3 t4 : Nat) : Bool :=
  siftPf LR TRI BP 5 0 (gptR t0 t1 t2 t3 t4)

end CFSG.KS.SporSch

end
