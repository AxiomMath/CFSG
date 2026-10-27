module

public import Certificates.Data.Kernel.Spor.Raw

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def trAt (n nw : Nat) (LR TR : Nat → Nat) (i k : Nat) : Nat :=
  TR (Nat.add (roff n nw (LR i)) k)

@[expose] noncomputable def gpt (w m t0 t1 t2 t3 t4 i : Nat) : Nat :=
  pg w m t0 (pg w m t1 (pg w m t2 (pg w m t3 (pg w m t4 i))))

@[expose] noncomputable def e5ab (n nw : Nat) (LR TR : Nat → Nat)
    (Q : Nat → Nat → Nat → Nat → Nat → Nat → Bool) (a b : Nat) : Bool :=
  strictB (rcnt (LR 1)) (fun c1 => strictB (rcnt (LR 2)) (fun c2 =>
  strictB (rcnt (LR 3)) (fun c3 => strictB (rcnt (LR 4)) (fun c4 =>
  strictB (trAt n nw LR TR 0 a) (fun t0 => strictB (trAt n nw LR TR 1 b) (fun t1 =>
  strictB (Nat.add (Nat.mul a c1) b) (fun k1 =>
  allN c2 (fun c => strictB (trAt n nw LR TR 2 c) (fun t2 =>
  strictB (Nat.add (Nat.mul k1 c2) c) (fun k2 =>
  allN c3 (fun d => strictB (trAt n nw LR TR 3 d) (fun t3 =>
  strictB (Nat.add (Nat.mul k2 c3) d) (fun k3 =>
  allN c4 (fun e => strictB (trAt n nw LR TR 4 e) (fun t4 =>
    Q (Nat.add (Nat.mul k3 c4) e) t0 t1 t2 t3 t4)))))))))))))))

@[expose] noncomputable def all5K (n nw : Nat) (LR TR : Nat → Nat)
    (Q : Nat → Nat → Nat → Nat → Nat → Nat → Bool) : Bool :=
  allN (rcnt (LR 0)) (fun a => allN (rcnt (LR 1)) (fun b => e5ab n nw LR TR Q a b))

@[expose] noncomputable def prod5K (n w m t0 t1 t2 t3 t4 : Nat) : Nat :=
  pcomp n w m (pcomp n w m (pcomp n w m (pcomp n w m t0 t1) t2) t3) t4

@[expose] noncomputable def prodCode (n w m nw : Nat) (LR TR : Nat → Nat) (k : Nat) : Nat :=
  strictN (rcnt (LR 1)) (fun c1 => strictN (rcnt (LR 2)) (fun c2 =>
  strictN (rcnt (LR 3)) (fun c3 => strictN (rcnt (LR 4)) (fun c4 =>
  strictN (Nat.div k c4) (fun k3 => strictN (Nat.div k3 c3) (fun k2 =>
  strictN (Nat.div k2 c2) (fun k1 => strictN (Nat.div k1 c1) (fun a =>
  prod5K n w m (trAt n nw LR TR 0 a) (trAt n nw LR TR 1 (Nat.mod k1 c1))
    (trAt n nw LR TR 2 (Nat.mod k2 c2)) (trAt n nw LR TR 3 (Nat.mod k3 c3))
    (trAt n nw LR TR 4 (Nat.mod k c4))))))))))

@[expose] noncomputable def tot5 (LR : Nat → Nat) : Nat :=
  Nat.mul (Nat.mul (Nat.mul (Nat.mul (rcnt (LR 0)) (rcnt (LR 1))) (rcnt (LR 2))) (rcnt (LR 3)))
    (rcnt (LR 4))

@[expose] noncomputable def maskOf (C : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun c _ ih => Nat.lor ih (Nat.shiftLeft (nat_lit 1) c)) C

@[expose] noncomputable def ascK (T : Nat) (C : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun c _ ih lo => bAnd(Nat.ble lo c, bAnd(Nat.blt c T, ih (Nat.succ c)))) C

@[expose] noncomputable def zipK (f : Nat → Nat → Bool) (C : List Nat) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun L => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) L)
    (fun c _ ih L => List.rec (motive := fun _ => Bool) false (fun l L' _ => bAnd(f c l, ih L')) L)
    C

@[expose] noncomputable def allL (f : Nat → Bool) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => bAnd(f x, ih)) L

@[expose] noncomputable def pairNe (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun x xs ih => bAnd(allL (fun y => bIf(Nat.beq x y, false, true)) xs, ih)) L

@[expose] noncomputable def survQ (P : Nat → Nat → Nat → Nat → Nat → Bool) (M : Nat)
    (code t0 t1 t2 t3 t4 : Nat) : Bool :=
  bIf(P t0 t1 t2 t3 t4, hasBit M code, bIf(hasBit M code, false, true))

@[expose] noncomputable def commPts (n w m G t0 t1 t2 t3 t4 : Nat) : Bool :=
  allN n (fun i => Nat.beq (gpt w m t0 t1 t2 t3 t4 (pg w m G i)) (pg w m G (gpt w m t0 t1 t2 t3 t4 i)))

@[expose] noncomputable def commAllPts (n w m : Nat) (G : Nat → Nat) (k t0 t1 t2 t3 t4 : Nat) :
    Bool :=
  allN k (fun j => commPts n w m (G j) t0 t1 t2 t3 t4)

@[expose] noncomputable def eqPts (n w m Z t0 t1 t2 t3 t4 : Nat) : Bool :=
  allN n (fun i => Nat.beq (gpt w m t0 t1 t2 t3 t4 i) (pg w m Z i))

@[expose] noncomputable def sqPts (n w m t0 t1 t2 t3 t4 : Nat) : Bool :=
  allN n (fun i => Nat.beq (gpt w m t0 t1 t2 t3 t4 (gpt w m t0 t1 t2 t3 t4 i)) i)

@[expose] noncomputable def sqGPts (n w m G t0 t1 t2 t3 t4 : Nat) : Bool :=
  allN n (fun i => strictB (gpt w m t0 t1 t2 t3 t4 (pg w m G i)) (fun j =>
    Nat.beq (gpt w m t0 t1 t2 t3 t4 (pg w m G j)) i))

@[expose] noncomputable def conjPts (n w m T y t0 t1 t2 t3 t4 : Nat) : Bool :=
  allN n (fun i => Nat.beq (gpt w m t0 t1 t2 t3 t4 (pg w m T i)) (pg w m y (gpt w m t0 t1 t2 t3 t4 i)))

@[expose] noncomputable def memPts (n w m : Nat) (L : List Nat) (t0 t1 t2 t3 t4 : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun y _ ih => bIf(eqPts n w m y t0 t1 t2 t3 t4, true, ih)) L

end CFSG.KS.SporSch

end
