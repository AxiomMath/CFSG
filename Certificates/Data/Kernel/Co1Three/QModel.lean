module

public import Certificates.Data.Kernel.Co1Three.Slp
public import Certificates.Data.Kernel.SporSch.Co1MatW

public section

namespace CFSG.KC.Co1Cl

open CFSG.KC.Enum CFSG.KC.Co1F2 CFSG.KC.Co1B CFSG.KS.SporSch.M24

@[expose] noncomputable def mdlK (TS : Nat → Nat) (p P tb : Nat) (G : List Nat) (c : Nat) : Nat :=
  mulWK (TS (Nat.add tb (Nat.div c P))) (epK TS p G (Nat.mod c P) oneK)

@[expose] noncomputable def addTK (ADT x y : Nat) : Nat :=
  Nat.add (fld(ADT, Nat.mul (nat_lit 5) (Nat.add (Nat.mul (nat_lit 27) (Nat.mod x (nat_lit 27)))
      (Nat.mod y (nat_lit 27))), nat_lit 31))
    (Nat.mul (nat_lit 27) (fld(ADT, Nat.mul (nat_lit 5) (Nat.add (Nat.mul (nat_lit 27)
      (Nat.div x (nat_lit 27))) (Nat.div y (nat_lit 27))), nat_lit 31)))

@[expose] noncomputable def adtQK (ADT : Nat) : Bool :=
  allN (nat_lit 729) fun i => Nat.beq (fld(ADT, Nat.mul (nat_lit 5) i, nat_lit 31))
    (addVK (nat_lit 3) (nat_lit 3) (Nat.div i (nat_lit 27)) (Nat.mod i (nat_lit 27)))

@[expose] noncomputable def lowJK (f : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun _ ih v => nIf(Nat.beq (Nat.mod v (nat_lit 3)) (nat_lit 0),
      Nat.succ (ih (Nat.div v (nat_lit 3))), nat_lit 0)) f

@[expose] noncomputable def atQK (N ADT : Nat) (A : List (List Nat)) (AT : List Nat) : Bool :=
  bAnd(Nat.beq (lenL AT) N, allN N fun l => strictB (getL (nat_lit 0) AT l) fun T =>
    allN (nat_lit 729) fun v => bIf(Nat.beq v (nat_lit 0),
      Nat.beq (Nat.land T (nat_lit 1023)) (nat_lit 0),
      strictB (lowJK (nat_lit 6) v) fun j =>
        Nat.beq (fld(T, Nat.mul (nat_lit 10) v, nat_lit 1023))
          (addTK ADT (fld(T, Nat.mul (nat_lit 10) (Nat.sub v (Nat.pow (nat_lit 3) j)), nat_lit 1023))
            (getL (nat_lit 0) (getLL A l) j))))

@[expose] noncomputable def mulQK (ADT : Nat) (TT : List (List Nat)) (AT : List Nat) (x y : Nat) :
    Nat :=
  strictN (Nat.div x (nat_lit 729)) fun k => strictN (Nat.mod x (nat_lit 729)) fun v =>
  strictN (Nat.div y (nat_lit 729)) fun l => strictN (Nat.mod y (nat_lit 729)) fun w =>
  strictN (getL (nat_lit 0) (getLL TT k) l) fun t =>
    Nat.add (Nat.mul (nat_lit 729) (Nat.div t (nat_lit 729)))
      (addTK ADT (addTK ADT (Nat.mod t (nat_lit 729)) w)
        (fld(getL (nat_lit 0) AT l, Nat.mul (nat_lit 10) v, nat_lit 1023)))

@[expose] noncomputable def relQK (P N tb qb : Nat) (Q : List (List Nat)) (RL : List Nat) : Bool :=
  allN (Nat.mul (nat_lit 2) N) fun i =>
    strictB (getL (nat_lit 0) RL i) fun r =>
    bAnd(Nat.blt r (Nat.mul P N),
      eqLK (getLL Q i) [Nat.mul (nat_lit 2) (Nat.add tb (Nat.div i (nat_lit 2))),
        Nat.mul (nat_lit 2) (Nat.add qb (Nat.mod i (nat_lit 2))),
        Nat.add (Nat.mul (nat_lit 8) (Nat.mod r P)) (nat_lit 1),
        Nat.mul (nat_lit 2) (Nat.add tb (Nat.div r P))])

@[expose] noncomputable def tabEntK (p n P N : Nat) (A B : List (List Nat)) (RL W : List Nat)
    (TT : List (List Nat)) (k l : Nat) : Bool :=
  strictB (getL (nat_lit 0) (getLL TT k) l) fun e =>
  bAnd(Nat.blt e (Nat.mul P N),
    bIf(Nat.beq l (nat_lit 0), Nat.beq e (Nat.mul P k),
      strictB (getL (nat_lit 0) W l) fun c =>
      strictB (fld(c, nat_lit 1, nat_lit 1048575)) fun r₁ =>
      strictB (Nat.shiftRight c (nat_lit 21)) fun j =>
      bAnd(Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 0),
      bAnd(Nat.ble (nat_lit 3) r₁, bAnd(Nat.blt (Nat.sub r₁ (nat_lit 3)) l,
      bAnd(Nat.blt j (nat_lit 2),
        strictB (getL (nat_lit 0) (getLL TT k) (Nat.sub r₁ (nat_lit 3))) fun t =>
        strictB (getL (nat_lit 0) RL
          (Nat.add (Nat.mul (nat_lit 2) (Nat.div t P)) j)) fun r =>
        strictB (Nat.div r P) fun m' =>
          Nat.beq e (Nat.add (Nat.mul P m')
            (actK p n (getLL A m') (Nat.mod r P)
              (actK p n (getLL B j) (Nat.mod t P) (nat_lit 0))))))))))

@[expose] noncomputable def tabQK (p n P N : Nat) (A B : List (List Nat)) (RL W : List Nat)
    (TT : List (List Nat)) : Bool :=
  bAnd(Nat.beq (lenLL TT) N,
    allN N fun k => bAnd(Nat.beq (lenL (getLL TT k)) N,
      allN N fun l => tabEntK p n P N A B RL W TT k l))

@[expose] noncomputable def fusFromK (N ADT : Nat) (TT : List (List Nat)) (AT GC RP : List Nat)
    (DP k : Nat) : List Nat → Nat → Bool :=
  fun FL => List.rec (motive := fun _ => Nat → Bool) (fun v => Nat.beq v (nat_lit 729))
    (fun f _ ih v => strictB v fun v => strictB (Nat.add (Nat.mul (nat_lit 729) k) v) fun x =>
      strictB (depK DP x) fun d =>
      bAnd(bIf(Nat.beq d (nat_lit 0),
          strictB (mulQK ADT TT AT x x) fun x₂ =>
            Bool.not (Nat.beq (mulQK ADT TT AT x₂ x) (nat_lit 0)),
        bIf(Nat.beq d (nat_lit 1), memK x RP,
          strictB (Nat.div f (nat_lit 8)) fun c => strictB (Nat.mod f (nat_lit 8)) fun g =>
          strictB (getL (nat_lit 0) GC g) fun h =>
          bAnd(Nat.blt g (lenL GC), bAnd(Nat.ble (nat_lit 729) c,
          bAnd(Nat.blt c (Nat.mul (nat_lit 729) N), bAnd(Nat.beq (Nat.succ (depK DP c)) d,
            Nat.beq (mulQK ADT TT AT x h) (mulQK ADT TT AT h c))))))),
        ih (Nat.succ v))) FL

@[expose] noncomputable def fusQK (N ADT : Nat) (TT : List (List Nat)) (AT GC RP : List Nat)
    (DP k : Nat) (FL : List Nat) : Bool :=
  fusFromK N ADT TT AT GC RP DP k FL (nat_lit 0)

end CFSG.KC.Co1Cl

end
