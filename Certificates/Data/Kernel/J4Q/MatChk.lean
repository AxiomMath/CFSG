module

public import Certificates.Data.Kernel.J4Q.Mat
public import Certificates.Data.CFSGNative.J4.Cert

public section

namespace CFSG.KC.J4Q

open CFSG.Sporadic.J4.Native

structure MatData where
  c : Nat
  rm : Nat
  one : Nat
  pad : Nat
  t0 : Nat
  t1 : Nat
  t2 : Nat
  t3 : Nat
  t4 : Nat
  t5 : Nat
  t6 : Nat
  LA : List Char
  LB : List Char
  A : Nat
  B : Nat
  Ai : Nat
  Bi : Nat
  L : List Nat
  Li : List Nat
  C : Nat
  Ci : Nat
  F : Nat

@[expose] noncomputable def MatData.consts (D : MatData) : Bool :=
  constsOK D.c D.rm D.one D.pad D.t0 D.t1 D.t2 D.t3 D.t4 D.t5 D.t6

@[expose] noncomputable def MatData.seeds (D : MatData) : Bool :=
  andB (decOK D.A D.LA) (decOK D.B D.LB)

@[expose] noncomputable def MatData.invs (D : MatData) : Bool :=
  andB (andB (canonJ D.pad D.Ai) (canonJ D.pad D.Bi))
    (andB (Nat.beq (mulJ D.c D.rm D.A D.Ai) D.one) (Nat.beq (mulJ D.c D.rm D.B D.Bi) D.one))

@[expose] noncomputable def locRun (D : MatData) (r : Nat) (ws : List (List Int)) :
    List Nat → List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → List Nat → Bool)
    (fun L Li => List.rec (motive := fun _ => Bool)
      (List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) Li) (fun _ _ _ => false) L)
    (fun w _ ih L Li => List.rec (motive := fun _ => Bool) false
      (fun x L' _ => List.rec (motive := fun _ => Bool) false
        (fun xi Li' _ => andB (Nat.beq x (wordJ D.c D.rm D.one [D.A, D.B] [D.Ai, D.Bi] w))
          (andB (andB (canonJ D.pad xi) (Nat.beq (mulJ D.c D.rm x xi) D.one))
            (andB (Nat.beq (vecJ D.rm r x) r) (ih L' Li')))) Li) L)
    ws

@[expose] noncomputable def MatData.loc (D : MatData) : Bool :=
  locRun D (v2N rootV) (localWords ()) D.L D.Li

@[expose] noncomputable def MatData.pows (D : MatData) : Bool :=
  strictB (mulJ D.c D.rm D.A D.B) fun AB =>
    andB (Nat.beq (mulJ D.c D.rm D.A D.A) D.one) (andB (neN D.A D.one)
    (andB (Nat.beq (powJ D.c D.rm D.one D.B (nat_lit 4)) D.one)
    (andB (neN (mulJ D.c D.rm D.B D.B) D.one)
    (andB (Nat.beq (powJ D.c D.rm D.one AB (nat_lit 37)) D.one) (neN AB D.one)))))

@[expose] noncomputable def MatData.conj (D : MatData) : Bool :=
  strictB (mulJ D.c D.rm (mulJ D.c D.rm (mulJ D.c D.rm D.A D.Ci) (mulJ D.c D.rm D.A D.B)) D.C)
    fun z => andB (Nat.beq D.C (wordJ D.c D.rm D.one [D.A, D.B] [D.Ai, D.Bi] (conjWord ())))
    (andB (andB (canonJ D.pad D.Ci) (Nat.beq (mulJ D.c D.rm D.C D.Ci) D.one))
    (andB (Nat.beq (powJ D.c D.rm D.one z (nat_lit 43)) D.one) (neN z D.one)))

@[expose] noncomputable def MatData.form (D : MatData) : Bool :=
  andB (packOK D.F formRows.toList)
    (andB (Nat.beq (mulJ D.c D.rm (mulJ D.c D.rm D.A D.F) (trJ D.t0 D.t1 D.t2 D.t3 D.t4 D.t5 D.t6 D.A)) D.F)
      (Nat.beq (mulJ D.c D.rm (mulJ D.c D.rm D.B D.F) (trJ D.t0 D.t1 D.t2 D.t3 D.t4 D.t5 D.t6 D.B)) D.F))

end CFSG.KC.J4Q

end
