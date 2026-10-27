module

public import Certificates.Data.Kernel.Spor.Raw

public section

namespace CFSG.KLC.E8

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def cf (K k : Nat) : Nat := pg (nat_lit 4) (nat_lit 15) K k

@[expose] noncomputable def sumN (n : Nat) (f : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun k ih => Nat.add (f k) ih) n

@[expose] noncomputable def REP : Nat := nat_lit 286331153

@[expose] noncomputable def HI : Nat := nat_lit 2290649224

@[expose] noncomputable def small (Y : Nat) : Bool :=
  bAnd(Nat.beq (Nat.land Y HI) (nat_lit 0), Nat.beq (Nat.land (Nat.add Y (Nat.mul (nat_lit 3) REP)) HI) (nat_lit 0))

@[expose] noncomputable def bindRow (K : Nat) (v : List Int) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun k => Nat.beq k (nat_lit 8))
    (fun c _ ih k => bAnd(Int.beq' c (Int.subNatNat (cf K k) (nat_lit 2)), ih (Nat.succ k))) v
    (nat_lit 0)

@[expose] noncomputable def bindRoots (RK : Nat → Nat) (L : List (List Int)) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun i => Nat.beq i (nat_lit 240))
    (fun v _ ih i => bAnd(Nat.blt (RK i) (nat_lit 4294967296), bAnd(small (RK i),
      bAnd(bindRow (RK i) v, ih (Nat.succ i))))) L (nat_lit 0)

@[expose] noncomputable def sortedOK (RK : Nat → Nat) (SO : Nat) : Bool :=
  bAnd(allN (nat_lit 240) (fun t => Nat.blt (pg (nat_lit 8) (nat_lit 255) SO t) (nat_lit 240)),
    allN (nat_lit 239) (fun t => Nat.blt (RK (pg (nat_lit 8) (nat_lit 255) SO t))
      (RK (pg (nat_lit 8) (nat_lit 255) SO (Nat.succ t)))))

@[expose] noncomputable def keyIf (Y : Nat) : Nat :=
  nIf(bAnd(Nat.blt Y (nat_lit 4294967296), small Y), Y, nat_lit 4294967296)

@[expose] noncomputable def key2 (neg : Bool) (x r : Nat) : Nat :=
  (fun ok => nIf(ok, sumN (nat_lit 8) fun k => Nat.shiftLeft
      (Bool.rec (motive := fun _ => Nat) (Nat.sub (Nat.add (cf x k) (nat_lit 4)) (Nat.mul (nat_lit 2) (cf r k)))
        (Nat.sub (Nat.add (cf x k) (Nat.mul (nat_lit 2) (cf r k))) (nat_lit 4)) neg)
      (Nat.mul (nat_lit 4) k), nat_lit 4294967296))
    (allN (nat_lit 8) fun k => Bool.rec (motive := fun _ => Bool)
      (bAnd(Nat.ble (Nat.mul (nat_lit 2) (cf r k)) (Nat.add (cf x k) (nat_lit 4)),
        Nat.ble (Nat.sub (Nat.add (cf x k) (nat_lit 4)) (Nat.mul (nat_lit 2) (cf r k))) (nat_lit 4)))
      (bAnd(Nat.ble (nat_lit 4) (Nat.add (cf x k) (Nat.mul (nat_lit 2) (cf r k))),
        Nat.ble (Nat.sub (Nat.add (cf x k) (Nat.mul (nat_lit 2) (cf r k))) (nat_lit 4)) (nat_lit 4)))
      neg)

@[expose] noncomputable def reflKey (x r : Nat) : Nat :=
  (fun P N => nIf(Nat.beq P N, x,
    nIf(Nat.beq P (Nat.add N (nat_lit 4)),
      nIf(Nat.ble r (Nat.add x (Nat.mul (nat_lit 2) REP)), keyIf (Nat.sub (Nat.add x (Nat.mul (nat_lit 2) REP)) r),
        nat_lit 4294967296),
    nIf(Nat.beq N (Nat.add P (nat_lit 4)),
      nIf(Nat.ble (Nat.mul (nat_lit 2) REP) (Nat.add x r), keyIf (Nat.sub (Nat.add x r) (Nat.mul (nat_lit 2) REP)),
        nat_lit 4294967296),
    nIf(Nat.beq P (Nat.add N (nat_lit 8)), key2 false x r,
    nIf(Nat.beq N (Nat.add P (nat_lit 8)), key2 true x r, nat_lit 4294967296))))))
    (Nat.add (sumN (nat_lit 8) fun k => Nat.mul (cf x k) (cf r k)) (nat_lit 32))
    (Nat.mul (nat_lit 2) (Nat.add (sumN (nat_lit 8) fun k => cf x k) (sumN (nat_lit 8) fun k => cf r k)))

@[expose] noncomputable def reflRowOK (RK : Nat → Nat) (r T : Nat) : Bool :=
  strictB (RK r) fun rk => allN (nat_lit 240) fun i => strictB (pg (nat_lit 8) (nat_lit 255) T i) fun e =>
    bAnd(Nat.blt e (nat_lit 240), Nat.beq (RK e) (reflKey (RK i) rk))

@[expose] noncomputable def negKey (x : Nat) : Nat := Nat.sub (Nat.mul (nat_lit 4) REP) x

@[expose] noncomputable def negTabOK (RK : Nat → Nat) (NEG : Nat) : Bool :=
  allN (nat_lit 240) fun i => strictB (pg (nat_lit 8) (nat_lit 255) NEG i) fun e =>
    bAnd(Nat.blt e (nat_lit 240), bAnd(small (RK i), Nat.beq (RK e) (negKey (RK i))))

@[expose] noncomputable def pop8 (m : Nat) : Nat :=
  sumN (nat_lit 8) fun k => Nat.land (Nat.shiftRight m k) (nat_lit 1)

@[expose] noncomputable def fieldMask (m : Nat) : Nat :=
  sumN (nat_lit 8) fun k => Nat.mul (Nat.land (Nat.shiftRight m k) (nat_lit 1))
    (Nat.shiftLeft (nat_lit 15) (Nat.mul (nat_lit 4) k))

@[expose] noncomputable def flipKey (m x : Nat) : Nat :=
  strictN (fieldMask m) fun F =>
    Nat.lor (Nat.sub x (Nat.land x F)) (Nat.land (negKey x) F)

@[expose] noncomputable def signRowOK (RK : Nat → Nat) (m T : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) true
    (allN (nat_lit 240) fun i => strictB (pg (nat_lit 8) (nat_lit 255) T i) fun e =>
      bAnd(Nat.blt e (nat_lit 240), bAnd(small (RK i), Nat.beq (RK e) (flipKey m (RK i)))))
    (Nat.beq (Nat.land (pop8 m) (nat_lit 1)) (nat_lit 0))

@[expose] noncomputable def fixCntK (n w p : Nat) : Nat :=
  sumN n fun i => nIf(Nat.beq (pg w (mask w) p i) i, nat_lit 1, nat_lit 0)

end CFSG.KLC.E8

end
