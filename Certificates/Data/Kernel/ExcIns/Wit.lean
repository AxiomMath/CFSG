module

public import Certificates.Data.Kernel.ExcExt.TabCheck

public section

namespace CFSG.ExcInsK

open CFSG.ExcExtK

@[expose] noncomputable def sgnEq (a b : Nat) (same : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) (Nat.beq (Nat.add a b) 16) (Nat.beq a b) same

@[expose] noncomputable def sgnOK (K : KT) (u s : Nat) : Bool :=
  allN K.r fun i => allN K.r fun j =>
    sgnEq (prK K (rtK K u i) (rtK K u j)) (prK K i j)
      (Bool.rec (motive := fun _ => Bool) (bnot (bit s j)) (bit s j) (bit s i))

@[expose] noncomputable def sgnsFrom (K : KT) (SG : List Nat) (n u : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun u => Nat.beq u n)
    (fun s _ ih u => band (sgnOK K u s) (ih (Nat.succ u))) SG u

structure KSat where
  b : List Nat
  E : Nat
  n : List (List Nat)
  k : List Nat
  B : Nat

inductive KRep where
  | sat (w : KSat)
  | flag (k : Nat)
  | a8

@[expose] noncomputable def offK : Nat := 4294967296

@[expose] noncomputable def plK (hx D i kk : Nat) : Nat := ln4 hx (Nat.add (Nat.mul D i) kk)

@[expose] noncomputable def lenK (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun _ _ acc => Nat.succ acc) l

@[expose] noncomputable def bOK (r c : Nat) (b : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ acc => band (band (Nat.blt a r) (bit c a)) acc) b

@[expose] noncomputable def ltOK (r : Nat) (k : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ acc => band (Nat.blt a r) acc) k

@[expose] noncomputable def dotK (hx D kk : Nat) (row b : List Nat) : Nat :=
  List.rec (motive := fun _ => List Nat → Nat) (fun _ => 0)
    (fun N _ ih bl => List.rec (motive := fun _ => Nat) 0
      (fun ba bt _ => Nat.add (Nat.mul N (plK hx D ba kk)) (ih bt)) bl) row b

@[expose] noncomputable def sumL (row : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun N _ acc => Nat.add N acc) row

@[expose] noncomputable def sumP (hx D kk : Nat) (b : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun ba _ acc => Nat.add (plK hx D ba kk) acc) b

@[expose] noncomputable def identK (hx D E rho i kk : Nat) (row b : List Nat) : Bool :=
  Nat.beq
    (Nat.add (Nat.add (dotK hx D kk row b) (Nat.mul (Nat.mul 8 offK) rho))
      (Nat.add (Nat.mul 8 E) (Nat.mul offK (plK hx D i kk))))
    (Nat.add (Nat.add (Nat.mul E (plK hx D i kk)) (Nat.mul 8 offK))
      (Nat.add (Nat.mul 8 (sumL row)) (Nat.mul offK (sumP hx D kk b))))

@[expose] noncomputable def rowsFrom (r hx D E rho c : Nat) (b : List Nat) (n : List (List Nat))
    (i : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun i => Nat.beq i r)
    (fun row _ ih i => band
      (bor (bnot (bit c i)) (band (Nat.beq (lenK row) rho)
        (allN D fun kk => identK hx D E rho i kk row b)))
      (ih (Nat.succ i))) n i

@[expose] noncomputable def invRow (K : KT) (B a bj : Nat) (k : List Nat) (l : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun kl _ ih l => Nat.add (Nat.mul (ln2 B (Nat.add (Nat.mul 8 a) l)) (Nat.succ (prK K kl bj)))
      (ih (Nat.succ l))) k l

@[expose] noncomputable def invCols (K : KT) (B a : Nat) (k b : List Nat) (j : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun bj _ ih j => band
      (Nat.beq (Nat.mod (Nat.add (invRow K B a bj k 0) (nif (Nat.beq a j) 2 0)) 3) 0)
      (ih (Nat.succ j))) b j

@[expose] noncomputable def satK (K : KT) (hx D c : Nat) (w : KSat) : Bool :=
  band (Nat.ble (lenK w.b) 8) <| band (bOK K.r c w.b) <|
  band (bnot (Nat.beq (Nat.mod (Nat.add w.E 2) 3) 0)) <|
  band (rowsFrom K.r hx D w.E (lenK w.b) c w.b w.n 0) <|
  band (Nat.beq (lenK w.k) (lenK w.b)) <| band (ltOK K.r w.k) <|
  allN (lenK w.b) fun a => invCols K w.B a w.k w.b 0

@[expose] noncomputable def orthK (K : KT) (k : Nat) : Nat :=
  maskK K.r fun i => band (Nat.beq (prK K k i) 8) (Nat.beq (prK K i k) 8)

@[expose] noncomputable def flagK (K : KT) (c k : Nat) : Bool :=
  bor (Nat.beq (truncK K.r c) (Nat.sub (Nat.shiftLeft 1 K.r) 1))
    (band (Nat.blt k K.r) (Nat.beq (truncK K.r c) (orthK K k)))

@[expose] noncomputable def repK (K : KT) (hx D : Nat) (e6 : Bool) (c : Nat) : KRep → Bool :=
  fun x => KRep.rec (motive := fun _ => Bool) (fun w => satK K hx D c w)
    (fun k => band e6 (flagK K c k)) false x

end CFSG.ExcInsK

end
