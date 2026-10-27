module

public import Certificates.Data.Kernel.ExcIns.Grow
public import Certificates.Data.Kernel.ExcIns.Wit

public section

namespace CFSG.ExcInsK

open CFSG.ExcExtK

structure KA8 where
  b : List Nat
  sp : List Nat
  cz : Nat
  hyp : List (Nat × List (Nat × Nat))

structure KA8R where
  img : List Nat
  w : KA8

@[expose] noncomputable def qlK (fx D i kk : Nat) : Nat := ln4 fx (Nat.add (Nat.mul D i) kk)

@[expose] noncomputable def chainS (fx D a a' kk : Nat) (b : List Nat) (s : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun bs _ ih s => Nat.add (nif (band (Nat.ble a s) (Nat.blt s a')) (qlK fx D bs kk) 0)
      (ih (Nat.succ s))) b s

@[expose] noncomputable def spanOK (fx D i e : Nat) (b : List Nat) : Bool :=
  band (Nat.blt e 512) <|
  band (Nat.blt (Nat.mod e 16) (Nat.mod (Nat.div e 16) 16)) <|
  band (Nat.ble (Nat.mod (Nat.div e 16) 16) 8) <|
  allN D fun kk =>
    Bool.rec (motive := fun _ => Bool)
      (Nat.beq (Nat.add (qlK fx D i kk)
          (Nat.mul 8 (Nat.sub (Nat.mod (Nat.div e 16) 16) (Nat.mod e 16))))
        (Nat.add (chainS fx D (Nat.mod e 16) (Nat.mod (Nat.div e 16) 16) kk b 0) 8))
      (Nat.beq (Nat.add (qlK fx D i kk) (chainS fx D (Nat.mod e 16) (Nat.mod (Nat.div e 16) 16) kk b 0))
        (Nat.add 8 (Nat.mul 8 (Nat.sub (Nat.mod (Nat.div e 16) 16) (Nat.mod e 16)))))
      (Nat.beq (Nat.div e 256) 1)

@[expose] noncomputable def spansFrom (r fx D c : Nat) (b sp : List Nat) (i : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun i => Nat.beq i r)
    (fun e _ ih i => band (bor (bnot (bit c i)) (spanOK fx D i e b)) (ih (Nat.succ i))) sp i

@[expose] noncomputable def gramL (a a' : Nat) : Nat :=
  nif (Nat.beq a a') 10 (nif (bor (Nat.beq (Nat.succ a) a') (Nat.beq (Nat.succ a') a)) 7 8)

@[expose] noncomputable def gramRow (K : KT) (a ba : Nat) (b : List Nat) (a' : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun bb _ ih a' => band (Nat.beq (prK K ba bb) (gramL a a')) (ih (Nat.succ a'))) b a'

@[expose] noncomputable def gramK (K : KT) (b0 b : List Nat) (a : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun ba _ ih a => band (gramRow K a ba b0 0) (ih (Nat.succ a))) b a

@[expose] noncomputable def expK (K : KT) (t : Nat) (b : List Nat) (a : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun ba _ ih a => Nat.add (Nat.mul (Nat.succ a) (prK K t ba)) (ih (Nat.succ a))) b a

@[expose] noncomputable def evK (K : KT) (t cz : Nat) : Nat :=
  Nat.mod (sumN K.d fun k => Nat.mul (fK K t k) (digK cz k)) 3

@[expose] noncomputable def expT (K : KT) (t cz X : Nat) : Bool :=
  band (Nat.beq (Nat.mod X 3) 0) (Nat.beq (Nat.mod (Nat.div X 3) 3) (evK K t cz))

@[expose] noncomputable def coefSum (K : KT) (k' : Nat) (coef : List (Nat × Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun e _ acc => Prod.rec (motive := fun _ => Nat) (fun i a => Nat.add acc (Nat.mul a (hK K i k'))) e)
    coef

@[expose] noncomputable def coefOK (r c : Nat) (coef : List (Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun e _ acc => Prod.rec (motive := fun _ => Bool)
      (fun i _ => band (band (Nat.blt i r) (bit c i)) acc) e) coef

@[expose] noncomputable def hypFrom (K : KT) (d r c cz : Nat) (hyp : List (Nat × List (Nat × Nat)))
    (k : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun k => Nat.beq k d)
    (fun hk _ ih k => band (Prod.rec (motive := fun _ => Bool) (fun x coef =>
      band (Nat.blt x 3) <| band (coefOK r c coef) <|
        allN d fun k' => Nat.beq (Nat.mod (Nat.add (coefSum K k' coef)
          (Nat.mul 2 (Nat.mod (Nat.add (nif (Nat.beq k k') 1 0) (Nat.mul (Nat.sub 3 x) (digK cz k'))) 3)))
          3) 0) hk) (ih (Nat.succ k))) hyp k

@[expose] noncomputable def a8K (K : KT) (fx D d c : Nat) (w : KA8) : Bool :=
  band (Nat.beq (lenK w.b) 8) <| band (bOK K.r c w.b) <| band (gramK K w.b w.b 0) <|
  band (spansFrom K.r fx D c w.b w.sp 0) <| band (Nat.blt w.cz (Nat.pow 3 d)) <|
  band (allN K.r fun t => expT K t w.cz (expK K t w.b 0)) (hypFrom K d K.r c w.cz w.hyp 0)

@[expose] noncomputable def imgsFrom (K : KT) (AP n c : Nat) (img : List Nat) (u : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun u => Nat.beq u 8)
    (fun idx _ ih u => band (band (Nat.blt idx n) (Nat.beq (ln128 AP idx) (imgK (rowK K u) K.r c)))
      (ih (Nat.succ u))) img u

@[expose] noncomputable def recA (K : KT) (fx D d AP n i : Nat) (x : KA8R) : Bool :=
  band (a8K K fx D d (ln128 AP i) x.w) (imgsFrom K AP n (ln128 AP i) x.img 0)

@[expose] noncomputable def chunkK (K : KT) (fx D d AP n hi : Nat) (L : List KA8R) (i : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun i => Nat.beq i hi)
    (fun x _ ih i => band (recA K fx D d AP n i x) (ih (Nat.succ i))) L i

end CFSG.ExcInsK

end
