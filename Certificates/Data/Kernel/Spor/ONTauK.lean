module

public import Certificates.Data.Kernel.Spor.ONCK

public section

namespace CFSG.KS.ONC

open CFSG.KC.Enum CFSG.KS CFSG.KC.Ord

@[expose] noncomputable def seedL (a ai b bi : Nat) (z : Int) : Nat :=
  Int.rec (motive := fun _ => Nat) (fun n => nIf(Nat.beq n (nat_lit 1), a, nIf(Nat.beq n (nat_lit 2), b, bi)))
    (fun n => nIf(Nat.beq n (nat_lit 0), ai, bi)) z

@[expose] noncomputable def wordK (mul : Nat → Nat → Nat) (L : Int → Nat) (w : List Int) (acc : Nat) :
    Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun z _ ih acc => strictN (mul acc (L z)) ih) w acc

@[expose] noncomputable def genK (mul : Nat → Nat → Nat) (G : List Nat) (w : List Nat) (acc : Nat) :
    Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun i _ ih acc => strictN (mul acc (List.getD G i (nat_lit 0))) ih) w acc

@[expose] noncomputable def gensK (mul : Nat → Nat → Nat) (L : Int → Nat) (one : Nat)
    (gw : List (List Int)) (k : List Nat → Bool) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun G => k G.reverse)
    (fun w _ ih G => strictB (wordK mul L w one) fun g => ih (g :: G)) gw []

@[expose] noncomputable def pairsK (mul : Nat → Nat → Nat) (one : Nat) (G : List Nat)
    (ps : List (List Nat × List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun p _ ih => bAnd(Nat.beq (genK mul G p.1 one) (genK mul G p.2 one), ih)) ps

@[expose] noncomputable def relsK (FA FB : Nat → Nat) (gw : List (List Int))
    (ps : List (List Nat × List Nat)) : Bool :=
  strictB CS fun cs => strictB DS fun ds => strictB LL fun L => strictB HH fun H =>
  strictB CM fun cm => strictB RM fun rm => strictB ONE fun one =>
  strictB (batK cs ds FA (nat_lit 0) (nat_lit 154)) fun a =>
  strictB (batK cs ds FB (nat_lit 0) (nat_lit 154)) fun b =>
  strictB (mul3 L H cm rm (mul3 L H cm rm b b) b) fun bi =>
    bAnd(Nat.beq (mul3 L H cm rm a a) one, bAnd(Nat.beq (mul3 L H cm rm b bi) one,
      gensK (mul3 L H cm rm) (seedL a a b bi) one gw fun G => pairsK (mul3 L H cm rm) one G ps))

end CFSG.KS.ONC

end
