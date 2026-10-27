module

public import Init

public section

namespace CFSG.KC.ON8138

@[expose] noncomputable def andK (a b : Bool) : Bool := Bool.rec false b a

@[expose] noncomputable def orK (a b : Bool) : Bool := Bool.rec b true a

@[expose] noncomputable def notK (a : Bool) : Bool := Bool.rec true false a

@[expose] noncomputable def allK (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k acc => andK acc (f k)) n

@[expose] noncomputable def anyK (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun k acc => orK acc (f k)) n

@[expose] noncomputable def strictN (x : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) x

@[expose] noncomputable def bitK (m d : Nat) : Bool :=
  Nat.beq (Nat.land (nat_lit 1) (Nat.shiftRight m d)) (nat_lit 1)

@[expose] noncomputable def dg (c k : Nat) : Nat := Nat.mod (Nat.div c (Nat.pow (nat_lit 3) k)) (nat_lit 3)

@[expose] noncomputable def ent (a b k : Nat) : Nat :=
  Nat.mod
    (Nat.add
      (Nat.add (Nat.mul (dg a (Nat.mul (nat_lit 4) (Nat.div k (nat_lit 4)))) (dg b (Nat.mod k (nat_lit 4))))
        (Nat.mul (dg a (Nat.add (Nat.mul (nat_lit 4) (Nat.div k (nat_lit 4))) (nat_lit 1)))
          (dg b (Nat.add (nat_lit 4) (Nat.mod k (nat_lit 4))))))
      (Nat.add
        (Nat.mul (dg a (Nat.add (Nat.mul (nat_lit 4) (Nat.div k (nat_lit 4))) (nat_lit 2)))
          (dg b (Nat.add (nat_lit 8) (Nat.mod k (nat_lit 4)))))
        (Nat.mul (dg a (Nat.add (Nat.mul (nat_lit 4) (Nat.div k (nat_lit 4))) (nat_lit 3)))
          (dg b (Nat.add (nat_lit 12) (Nat.mod k (nat_lit 4)))))))
    (nat_lit 3)

@[expose] noncomputable def mulK (a b : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => Nat.add acc (Nat.mul (ent a b k) (Nat.pow (nat_lit 3) k))) (nat_lit 16)

@[expose] noncomputable def IK : Nat := nat_lit 14408200

@[expose] noncomputable def M0K : Nat := nat_lit 36709526

@[expose] noncomputable def M1K : Nat := nat_lit 706050

@[expose] noncomputable def powK (c k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) IK (fun _ acc => mulK acc c) k

@[expose] noncomputable def packL (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun x _ ih => Nat.add x (Nat.mul (nat_lit 3) ih)) l

@[expose] noncomputable def foldK (w : List Nat) (a : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun a => a)
    (fun k _ ih a => ih (mulK a (Bool.rec M1K M0K (Nat.beq k (nat_lit 0))))) w a

@[expose] noncomputable def memK (R0K : Nat → Nat) (c : Nat) : Bool :=
  anyK (nat_lit 320) fun k => Nat.beq (R0K k) c

@[expose] noncomputable def listOK (R0K : Nat → Nat) (L : List (List Nat)) (i : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun l _ ih i => andK (Nat.beq (R0K i) (packL l)) (ih (Nat.succ i))) L i

@[expose] noncomputable def r0OK (R0K R0I : Nat → Nat) (L : List (List Nat)) : Bool :=
  andK (listOK R0K L (nat_lit 0))
    (andK (memK R0K IK)
      (allK (nat_lit 320) fun i =>
        andK (memK R0K (mulK (R0K i) M0K))
          (andK (memK R0K (mulK (R0K i) M1K))
            (andK (Nat.blt (R0I i) (nat_lit 320)) (Nat.beq (mulK (R0K (R0I i)) (R0K i)) IK)))))

@[expose] noncomputable def wordsOK (W L : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => List (List Nat) → Bool) (fun _ => true)
    (fun w _ ih L => List.rec (motive := fun _ => Bool) false
      (fun l L' _ => andK (Nat.beq (foldK w IK) (packL l)) (ih L')) L) W L

@[expose] noncomputable def vd (x i : Nat) : Nat := dg x i

@[expose] noncomputable def pairK (x y : Nat) : Nat :=
  Nat.mod
    (Nat.add
      (Nat.add (Nat.mul (vd x 0) (vd y 3))
        (Nat.add (Nat.mul (nat_lit 2) (Nat.mul (vd x 1) (vd y 2)))
          (Nat.mul (nat_lit 2) (Nat.mul (vd x 1) (vd y 3)))))
      (Nat.add (Nat.mul (vd x 2) (vd y 1))
        (Nat.add (Nat.mul (nat_lit 2) (Nat.mul (vd x 3) (vd y 0))) (Nat.mul (vd x 3) (vd y 1)))))
    (nat_lit 3)

@[expose] noncomputable def maskOK (MK : Nat → Nat) : Bool :=
  allK (nat_lit 3) fun v => allK (nat_lit 81) fun x => allK (nat_lit 81) fun d =>
    Bool.rec (notK (bitK (MK (Nat.add (Nat.mul (nat_lit 81) v) x)) d))
      (bitK (MK (Nat.add (Nat.mul (nat_lit 81) v) x)) d) (Nat.beq (pairK x d) v)

@[expose] noncomputable def cosJ (R0K TK TI TW : Nat → Nat) (j : Nat) : Bool :=
  andK (Nat.beq (mulK (TI j) (TK j)) IK)
    (andK (notK (andK (memK R0K (mulK (mulK (TI j) M0K) (TK j)))
      (memK R0K (mulK (mulK (TI j) M1K) (TK j)))))
      (andK (Nat.blt (Nat.mod (TW j) (nat_lit 512)) (nat_lit 320))
        (andK (Nat.blt (Nat.div (TW j) (nat_lit 512)) (nat_lit 10))
          (strictN (powK (mulK (R0K (Nat.mod (TW j) (nat_lit 512))) (TK j))
              (Nat.div (TW j) (nat_lit 512))) fun B =>
            andK (notK (Nat.beq B IK)) (Nat.beq (powK B (nat_lit 3)) IK)))))

@[expose] noncomputable def cosOK (R0K TK TI TW : Nat → Nat) : Bool :=
  andK (Nat.beq (TK (nat_lit 0)) IK)
    (allK (nat_lit 161) fun j => cosJ R0K TK TI TW (Nat.succ j))

@[expose] noncomputable def findW (L key : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun _ ih L =>
      Bool.rec (ih (Nat.shiftRight L (nat_lit 30)))
        (Nat.shiftRight (Nat.land L (nat_lit 1073741823)) (nat_lit 13))
        (Nat.beq (Nat.land L (nat_lit 8191)) key)) (nat_lit 32) L

@[expose] noncomputable def codeK (a b c d : Nat) : Nat :=
  Nat.add a (Nat.mul (nat_lit 81) (Nat.add b (Nat.mul (nat_lit 81) (Nat.add c (Nat.mul (nat_lit 81) d)))))

@[expose] noncomputable def leafW (R0K TK : Nat → Nat) (a b c d w : Nat) : Bool :=
  andK (Nat.blt (Nat.mod w (nat_lit 512)) (nat_lit 320))
    (andK (Nat.blt (Nat.div w (nat_lit 512)) (nat_lit 162))
      (Nat.beq (mulK (R0K (Nat.mod w (nat_lit 512))) (TK (Nat.div w (nat_lit 512)))) (codeK a b c d)))

@[expose] noncomputable def leafK (R0K TK WK : Nat → Nat) (a b c d : Nat) : Bool :=
  strictN (findW (WK (Nat.add (Nat.mul (nat_lit 81) a) b)) (Nat.add (Nat.mul (nat_lit 81) c) d))
    fun w => leafW R0K TK a b c d w

@[expose] noncomputable def spA (R0K TK WK MK : Nat → Nat) (a : Nat) : Bool :=
  allK (nat_lit 81) fun b => orK (notK (bitK (MK a) b))
    (strictN (Nat.land (MK a) (MK (Nat.add (nat_lit 162) b))) fun mc =>
      allK (nat_lit 81) fun c => orK (notK (bitK mc c))
        (strictN (Nat.land (Nat.land (MK (Nat.add (nat_lit 81) a)) (MK (Nat.add (nat_lit 162) b)))
            (MK c)) fun md =>
          allK (nat_lit 81) fun d => orK (notK (bitK md d)) (leafK R0K TK WK a b c d)))

@[expose] noncomputable def spRange (R0K TK WK MK : Nat → Nat) (lo n : Nat) : Bool :=
  allK n fun k => spA R0K TK WK MK (Nat.add lo k)

end CFSG.KC.ON8138

end
