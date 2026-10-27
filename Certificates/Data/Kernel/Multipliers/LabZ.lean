module

public import CFSG.Certificates.Kernel.Common.LceSRange
public import CFSG.Certificates.Kernel.Bounds.HSAlt.Lab

public section

namespace CFSG.KC.LabZ

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS

@[expose] noncomputable def lanes (D v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => Nat.add acc (Nat.shiftLeft v (Nat.mul (nat_lit 48) k))) D

@[expose] noncomputable def constsOK (D BIAS Q HIGH TOP : Nat) : Bool :=
  andB (Nat.ble D (nat_lit 64))
  (andB (Nat.beq BIAS (lanes D (nat_lit 140737488355328)))
  (andB (Nat.beq Q (lanes D (nat_lit 16777216)))
  (andB (Nat.beq HIGH (lanes D (nat_lit 281474943156224)))
    (Nat.beq TOP (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 48) D))))))

@[expose] noncomputable def validZ (BIAS Q HIGH TOP x : Nat) : Bool :=
  andB (Nat.ble BIAS (Nat.add x Q))
    (andB (Nat.blt (Nat.sub (Nat.add x Q) BIAS) TOP)
      (Nat.beq (Nat.land (Nat.sub (Nat.add x Q) BIAS) HIGH) (nat_lit 0)))

@[expose] noncomputable def addF (BIAS S v : Nat) : Nat := Nat.sub (Nat.add S v) BIAS

@[expose] noncomputable def addB (BIAS S v : Nat) : Nat := Nat.sub (Nat.add S BIAS) v

@[expose] noncomputable def refLab (LB : Nat → Nat) (BIAS e acc : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (addF BIAS acc (LB (Nat.shiftRight e (nat_lit 1))))
    (addB BIAS acc (LB (Nat.shiftRight e (nat_lit 1))))
    (Nat.beq (Nat.land e (nat_lit 1)) (nat_lit 1))

@[expose] noncomputable def labGo (LB : Nat → Nat) (BIAS Li ft n : Nat) (k : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun k ih R acc => Bool.rec (motive := fun _ => Nat)
      (strictN (refLab LB BIAS (Nat.land R (nat_lit 4294967295)) acc)
        (ih (Nat.shiftRight R (nat_lit 32))))
      (strictN (addF BIAS acc Li) (ih R))
      (Nat.beq (Nat.sub n (Nat.succ k)) ft)) k

@[expose] noncomputable def labWalk (LB TG : Nat → Nat) (BIAS Q HIGH TOP i J wid w : Nat) : Bool :=
  letB (LB i) (fun Li =>
    andB (validZ BIAS Q HIGH TOP Li)
      (Nat.beq (labGo LB BIAS Li (Nat.land (Nat.shiftRight J (nat_lit 37)) (nat_lit 65535)) (wLen w)
          (wLen w) (Nat.shiftRight J (nat_lit 53)) BIAS)
        (TG wid)))

@[expose] noncomputable def labStep (LB TG : Nat → Nat) (BIAS Q HIGH TOP J S wid w : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 0)
    (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.succ S)
        (Nat.beq (LB (Nat.sub S (nat_lit 1))) BIAS))
      (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.succ S)
        (labWalk LB TG BIAS Q HIGH TOP (Nat.sub S (nat_lit 1)) J wid w))
      (Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1)))
    (Nat.blt (nat_lit 0) S)

@[expose] noncomputable def labChunk (WT LB TG : Nat → Nat) (BIAS Q HIGH TOP C S : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
    (fun _ ih J S => Bool.rec (motive := fun _ => Nat)
      (strictN (labStep LB TG BIAS Q HIGH TOP J S (nat_lit 0) (nat_lit 0))
        (ih (Nat.shiftRight J (nat_lit 1))))
      (strictN (Nat.land (Nat.shiftRight J (nat_lit 1)) (nat_lit 65535)) (fun wid =>
        strictN (WT wid) (fun w =>
          strictN (labStep LB TG BIAS Q HIGH TOP J S wid w) (ih (Nat.shiftRight J (jLen J w))))))
      (Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1)))
    (Nat.land C (nat_lit 255)) (Nat.shiftRight C (nat_lit 8)) S

@[expose] noncomputable def runLabZ (WT LB TG : Nat → Nat) (BIAS Q HIGH TOP : Nat) (Cs : List Nat) :
    Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun C _ ih S => strictN (labChunk WT LB TG BIAS Q HIGH TOP C S) ih) Cs

@[expose] noncomputable def tgOne (INV8 nR K BIAS w h t : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool) true
      (Bool.rec (motive := fun _ => Bool)
        (andB (Nat.blt h nR) (Nat.beq t (Nat.add BIAS (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 48) h)))))
        (Nat.beq t BIAS)
        (Nat.beq (freeRed INV8 (wWord w) (wLen w)) (nat_lit 0)))
      (Nat.beq (wKind w) (nat_lit 2)))
    (andB (Nat.blt h K)
      (Nat.beq t (Nat.add BIAS (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 48) (Nat.add nR h))))))
    (Nat.beq (wKind w) (nat_lit 3))

@[expose] noncomputable def tgOK (WT TG : Nat → Nat) (INV8 m Hs nR K D BIAS : Nat) : Bool :=
  andB (Nat.ble (Nat.add nR K) D)
    (Nat.rec (motive := fun _ => Bool) true (fun k ih => andB ih
      (tgOne INV8 nR K BIAS (WT k) (CFSG.KC.HSK.hint Hs k) (TG k))) m)

@[expose] noncomputable def cycLab (LB : Nat → Nat) (BIAS : Nat) (k : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun _ ih R acc => strictN (refLab LB BIAS (Nat.land R (nat_lit 4294967295)) acc)
        (ih (Nat.shiftRight R (nat_lit 32)))) k

@[expose] noncomputable def cycZ (blk WT LB : Nat → Nat) (BIAS nf c wid R V : Nat) : Bool :=
  letB (WT wid) (fun w => andB (Nat.beq (wKind w) (nat_lit 2))
    (andB (Nat.beq (CFSG.KC.HSK.cycWalk blk nf (wLen w) R (wStart c (wWord w)))
        (Nat.add c (nat_lit 1048576)))
      (Nat.beq (cycLab LB BIAS (wLen w) R BIAS) V)))

@[expose] noncomputable def coneOk (blk WT RT ST LB TG : Nat → Nat)
    (INV INV8 L nC nf m Hs K nR D BIAS Q HIGH TOP S0 S1 T0 T1 : Nat) (Cs : List Nat) : Bool :=
  andB (wordsOK WT RT ST INV INV8 m Hs)
  (andB (invOK INV INV8 L)
  (andB (Nat.ble nC (nat_lit 1048576))
  (andB (Nat.blt nf (nat_lit 4294967296))
  (andB (Nat.beq S0 (mkS (nat_lit 0) (nat_lit 1)))
  (andB (Nat.beq S1 (mkS nf nC))
  (andB (Nat.beq T0 (nat_lit 1))
  (andB (Nat.beq T1 (Nat.succ nf))
  (andB (CFSG.KC.HSK.hintsLt WT m K Hs)
  (andB (Nat.beq (CFSG.KC.LceSR.runIds WT m Cs (nat_lit 1)) (nat_lit 1))
  (andB (constsOK D BIAS Q HIGH TOP)
  (andB (tgOK WT TG INV8 m Hs nR K D BIAS)
  (andB (Nat.beq (runFacts blk WT INV nC L Cs S0) S1)
    (Nat.beq (runLabZ WT LB TG BIAS Q HIGH TOP Cs T0) T1)))))))))))))

end CFSG.KC.LabZ

end
