module

public import Certificates.Data.Kernel.Spor.ONK
public import Certificates.Data.Kernel.Spor.PEnum
public import CFSG.Certificates.Kernel.Orders.Mat
public import Certificates.Data.CFSGNative.Th.Tables

public section

namespace CFSG.KS.ONC

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KC.Ord CFSG.Sporadic.Th.Native

@[expose] noncomputable def CS : Nat := rep1 (nat_lit 1693) (nat_lit 154)

@[expose] noncomputable def DS : Nat := rep1 (nat_lit 1694) (nat_lit 154)

@[expose] noncomputable def LL : Nat := rep1 (nat_lit 11) (nat_lit 23716)

@[expose] noncomputable def HH : Nat := Nat.shiftLeft LL (nat_lit 10)

@[expose] noncomputable def CM : Nat := Nat.mul (nat_lit 2047) DS

@[expose] noncomputable def RM : Nat := Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 1694)) (nat_lit 1)

@[expose] noncomputable def ONE : Nat := rep1 (nat_lit 1705) (nat_lit 154)

@[expose] noncomputable def LV : Nat := rep1 (nat_lit 11) (nat_lit 154)

@[expose] noncomputable def HV : Nat := Nat.shiftLeft LV (nat_lit 10)

@[expose] noncomputable def spr (cs ds v : Nat) : Nat := Nat.land (Nat.mul v cs) ds

@[expose] noncomputable def colK (cs ds x i : Nat) : Nat :=
  Nat.shiftLeft (Nat.lor (spr cs ds (vP x)) (Nat.shiftLeft (spr cs ds (vM x)) (nat_lit 1)))
    (Nat.mul (nat_lit 11) i)

@[expose] noncomputable def batK (cs ds : Nat) (F : Nat → Nat) (lo cnt : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => strictN (colK cs ds (F (Nat.add lo i)) i) fun c => Nat.lor acc c) cnt

@[expose] noncomputable def redK (w L H p T x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) x
    (fun i acc => strictN acc fun a => csub w L H (Nat.shiftLeft p (Nat.sub T i)) a) (Nat.succ T)

@[expose] noncomputable def mulK (p w S d T L H CM RM A B : Nat) : Nat :=
  strictN (mulU w S d CM RM A B) fun u => redK w L H p T u

@[expose] noncomputable def mul3 (L H cm rm A B : Nat) : Nat :=
  mulK (nat_lit 3) (nat_lit 11) (nat_lit 1694) (nat_lit 154) (nat_lit 8) L H cm rm A B

@[expose] noncomputable def vld3 (L H X : Nat) : Bool := validM (nat_lit 3) (nat_lit 260876) L H X

@[expose] noncomputable def batCnt (n s : Nat) : Nat :=
  nIf(Nat.ble (Nat.mul (Nat.succ s) (nat_lit 154)) n, nat_lit 154, Nat.sub n (Nat.mul s (nat_lit 154)))

@[expose] noncomputable def letS (ML : Nat → Nat) (LT : Nat → Nat → Nat) (K : Nat → Nat) (n s : Nat) :
    Bool :=
  strictB CS fun cs => strictB DS fun ds => strictB LL fun L => strictB HH fun H =>
  strictB CM fun cm => strictB RM fun rm =>
  strictB (Nat.mul s (nat_lit 154)) fun lo => strictB (batCnt n s) fun cnt =>
  strictB (batK cs ds K lo cnt) fun X =>
    allN (nat_lit 4) fun j => Nat.beq (mul3 L H cm rm (ML j) X)
      (batK cs ds (fun x => K (LT (Nat.mul (nat_lit 2) j) x)) lo cnt)

@[expose] noncomputable def strictS {α : Type} (y : Nat) (k : Nat → α) : α :=
  Nat.rec (motive := fun _ => α) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def slpStep (mul : Nat → Nat → Nat) (vld : Nat → Bool) (one : Nat)
    (V : Nat → Nat) (st : List Nat × Nat × Bool) : Instr → List Nat × Nat × Bool
  | .mu i j k => strictS (mul (List.getD st.1 i (nat_lit 0)) (List.getD st.1 j (nat_lit 0))) fun x =>
      (List.set st.1 k x, st.2.1, st.2.2)
  | .pwr _ _ _ => (st.1, st.2.1, false)
  | .iv i k => strictS (V st.2.1) fun x =>
      (List.set st.1 k x, Nat.succ st.2.1,
        bAnd(st.2.2, bAnd(vld x, Nat.beq (mul (List.getD st.1 i (nat_lit 0)) x) one)))

@[expose] noncomputable def slpRun (mul : Nat → Nat → Nat) (vld : Nat → Bool) (one : Nat)
    (V : Nat → Nat) (fin : List Nat × Nat × Bool → Bool) :
    List Instr → List Nat × Nat × Bool → Bool :=
  List.rec (motive := fun _ => List Nat × Nat × Bool → Bool) fin
    (fun ins _ ih st => Prod.rec (motive := fun _ => Bool)
      (fun R rest => Prod.rec (motive := fun _ => Bool) (fun t ok => ih (R, t, ok)) rest)
      (slpStep mul vld one V st ins))

@[expose] noncomputable def selK (sel : List Nat) (ML : Nat → Nat) (R : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun s _ ih j => bAnd(Nat.beq (List.getD R s (nat_lit 0)) (ML j), ih (Nat.succ j))) sel (nat_lit 0)

@[expose] noncomputable def slpK (prog : List Instr) (nr : Nat) (FA FB V ML : Nat → Nat)
    (sel : List Nat) : Bool :=
  strictB CS fun cs => strictB DS fun ds => strictB LL fun L => strictB HH fun H =>
  strictB CM fun cm => strictB RM fun rm => strictB ONE fun one =>
  strictB (batK cs ds FA (nat_lit 0) (nat_lit 154)) fun a =>
  strictB (batK cs ds FB (nat_lit 0) (nat_lit 154)) fun mb =>
  strictB (mul3 L H cm rm (mul3 L H cm rm mb a) mb) fun b =>
    slpRun (mul3 L H cm rm) (vld3 L H) one V
      (fun st => bAnd(st.2.2, selK sel ML st.1)) prog
      (a :: b :: List.replicate (Nat.sub nr (nat_lit 2)) one, nat_lit 0, true)

end CFSG.KS.ONC

end
