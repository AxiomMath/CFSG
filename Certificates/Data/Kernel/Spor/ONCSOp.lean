module

public import Certificates.Data.Kernel.Spor.ONTauK
public import CFSG.RankThree.Native.ONTripleSLP
public import Mathlib

public section

namespace CFSG.KS.ONC

open CFSG.KC.Enum CFSG.KS CFSG.KC.Ord CFSG.RankThree.Native.ONTriple

@[expose] noncomputable def chunkK (FA FB : Nat → Nat) (w : List Int) (pre post : Nat) : Bool :=
  strictB CS fun cs => strictB DS fun ds => strictB LL fun L => strictB HH fun H =>
  strictB CM fun cm => strictB RM fun rm => strictB ONE fun one =>
  strictB (batK cs ds FA (nat_lit 0) (nat_lit 154)) fun a =>
  strictB (batK cs ds FB (nat_lit 0) (nat_lit 154)) fun b =>
  strictB (mul3 L H cm rm (mul3 L H cm rm b b) b) fun bi =>
    bAnd(Nat.beq (mul3 L H cm rm a a) one, bAnd(Nat.beq (mul3 L H cm rm b bi) one,
      Nat.beq (wordK (mul3 L H cm rm) (seedL a a b bi) w pre) post))

@[expose] noncomputable def letV (R : List Nat) (VI : Nat → Nat) (l : Nat × Bool) : Nat :=
  Bool.rec (motive := fun _ => Nat) (VI l.1) (List.getD R l.1 (nat_lit 0)) l.2

@[expose] noncomputable def recS (VI : Nat → Nat) (w : List (Nat × Bool)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun l _ ih => bAnd(Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) true false (Nat.beq (VI l.1) (nat_lit 0))) true l.2, ih)) w

@[expose] noncomputable def wordS (mul : Nat → Nat → Nat) (R : List Nat) (VI : Nat → Nat)
    (w : List (Nat × Bool)) (acc : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun l _ ih acc => strictN (mul acc (letV R VI l)) ih) w acc

@[expose] noncomputable def powS (mul : Nat → Nat → Nat) (x e acc : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) acc (fun _ a => strictN a fun y => mul y x) e

@[expose] noncomputable def invS (mul : Nat → Nat → Nat) (vld : Nat → Bool) (one : Nat)
    (VI : Nat → Nat) (r x : Nat) : Bool :=
  strictB (VI r) fun v =>
    bIf(Nat.beq v (nat_lit 0), true, bAnd(vld v, Nat.beq (mul x v) one))

@[expose] noncomputable def stepS (mul : Nat → Nat → Nat) (vld : Nat → Bool) (one : Nat)
    (VI : Nat → Nat) (st : List Nat × Bool) : SOp → List Nat × Bool
  | .word w => strictS (wordS mul st.1 VI w one) fun x =>
      (st.1 ++ [x], bAnd(st.2, bAnd(recS VI w, invS mul vld one VI st.1.length x)))
  | .pow e i => strictS (powS mul (List.getD st.1 i (nat_lit 0)) e one) fun x =>
      (st.1 ++ [x], bAnd(st.2, bAnd(Nat.blt i st.1.length, invS mul vld one VI st.1.length x)))

@[expose] noncomputable def runS (mul : Nat → Nat → Nat) (vld : Nat → Bool) (one : Nat)
    (VI : Nat → Nat) (fin : List Nat × Bool → Bool) : List SOp → List Nat × Bool → Bool :=
  List.rec (motive := fun _ => List Nat × Bool → Bool) fin
    (fun o _ ih st => Prod.rec (motive := fun _ => Bool) (fun R ok => ih (R, ok))
      (stepS mul vld one VI st o))

@[expose] noncomputable def initS (mul : Nat → Nat → Nat) (vld : Nat → Bool) (one : Nat)
    (VI : Nat → Nat) (R : List Nat) (n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun r ih => bAnd(invS mul vld one VI r (List.getD R r (nat_lit 0)), ih)) n

@[expose] noncomputable def sopK (init : List Nat) (VI : Nat → Nat)
    (fin : List Nat × Bool → Bool) (prog : List SOp) : Bool :=
  strictB LL fun L => strictB HH fun H => strictB CM fun cm => strictB RM fun rm =>
  strictB ONE fun one =>
    bAnd(initS (mul3 L H cm rm) (vld3 L H) one VI init init.length,
      runS (mul3 L H cm rm) (vld3 L H) one VI fin prog (init, true))

end CFSG.KS.ONC

end
