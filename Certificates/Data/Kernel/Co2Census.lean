module

public import Certificates.Data.Kernel.Co2J

public section

namespace CFSG.KC.Co2TInv

open CFSG.KC.Loop CFSG.KC.Co2InvS CFSG.KC.Co2J CFSG.KC.M1F2 CFSG.KLie.CT

@[expose] noncomputable def wProdR (MK : Nat → Nat) (n w acc : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun _ ih w acc => strictN (mulT (MK (Nat.land w (nat_lit 7))) acc) fun a =>
      ih (Nat.shiftRight w (nat_lit 3)) a)
    n w acc

@[expose] noncomputable def liftK (G MK PE JE CL LW LN LT SC : Nat → Nat) (s : Nat) : Bool :=
  andK (Nat.blt (CL s) (nat_lit 256)) (
  andK (Co2J.wordK G (LW s) (LN s) (LT s)) (
  andK (Nat.beq (wProdR MK (LN s) (LW s) IDT) (PE (CL s))) (
  andK (Nat.blt (SC s) (nat_lit 1024))
    (Nat.beq (mulV (LT s) (LT s)) (JE (SC s))))))

@[expose] noncomputable def liftAllK (G MK PE JE CL LW LN LT SC : Nat → Nat) (NR : Nat) : Bool :=
  allK NR (liftK G MK PE JE CL LW LN LT SC)

@[expose] noncomputable def addP (P v : Nat) : Nat := Nat.xor (vmF (nat_lit 10) P v) v

@[expose] noncomputable def repAt (R k : Nat) : Nat := fld(R, Nat.mul (nat_lit 10) k, nat_lit 1023)

@[expose] noncomputable def scanV (P c R n W v : Nat) : Bool :=
  implK (Nat.beq (addP P v) c)
    (letB (fld(W, Nat.mul (nat_lit 14) v, nat_lit 16383)) fun r =>
      letB (Nat.land r (nat_lit 15)) fun k =>
        andK (Nat.blt k n)
          (Nat.beq v (Nat.xor (repAt R k) (addP P (Nat.shiftRight r (nat_lit 4))))))

@[expose] noncomputable def scanK (PE CL SC RR RN SW : Nat → Nat) (s : Nat) : Bool :=
  letB (PE (CL s)) fun P => letB (SC s) fun c => letB (RR s) fun R => letB (RN s) fun n =>
    letB (SW s) fun W => allK (nat_lit 1024) (scanV P c R n W)

@[expose] noncomputable def scanAllK (PE CL SC RR RN SW : Nat → Nat) (NR : Nat) : Bool :=
  allK NR (scanK PE CL SC RR RN SW)

@[expose] noncomputable def fusV (PE INV CL FU : Nat → Nat) (NR q : Nat) : Bool :=
  letB (FU q) fun r => letB (Nat.land r (nat_lit 255)) fun u =>
    letB (Nat.shiftRight r (nat_lit 8)) fun s =>
      andK (Nat.blt s NR) (Nat.beq (mulT (PE u) (PE (INV q))) (mulT (PE (CL s)) (PE u)))

@[expose] noncomputable def fusCK (PE INV CL FU : Nat → Nat) (NR NI : Nat) : Bool :=
  allK NI (fusV PE INV CL FU NR)

@[expose] noncomputable def jorbV (PE JR JO : Nat → Nat) (NJ v : Nat) : Bool :=
  letB (JO v) fun r => letB (Nat.land r (nat_lit 255)) fun u =>
    letB (Nat.shiftRight r (nat_lit 8)) fun j =>
      andK (Nat.blt j NJ) (Nat.beq (vmF (nat_lit 10) (PE u) (JR j)) v)

@[expose] noncomputable def jorbK (PE JR JO : Nat → Nat) (NJ : Nat) : Bool :=
  andK (allK NJ fun j => Nat.blt (JR j) (nat_lit 1024))
    (rangeK (nat_lit 1) (nat_lit 1023) (jorbV PE JR JO NJ))

@[expose] noncomputable def lookV (CF : Nat → Nat → Nat) (NC : Nat → Nat) (X r : Nat) : Bool :=
  letB (Nat.land r (nat_lit 15)) fun c => letB (Nat.shiftRight r (nat_lit 4)) fun i =>
    andK (Nat.blt c (nat_lit 10)) (andK (Nat.blt i (NC c)) (Nat.beq (elemAt (CF c) i) X))

@[expose] noncomputable def lookAt (L k : Nat) : Nat :=
  fld(L, Nat.mul (nat_lit 24) k, nat_lit 16777215)

@[expose] noncomputable def lookK (CF : Nat → Nat → Nat) (NC JE LT RR RN LK : Nat → Nat) (s : Nat) :
    Bool :=
  letB (LT s) fun L => letB (RR s) fun R => letB (LK s) fun K =>
    allK (RN s) fun k => lookV CF NC (mulV (JE (repAt R k)) L) (lookAt K k)

@[expose] noncomputable def lookAllK (CF : Nat → Nat → Nat) (NC JE LT RR RN LK : Nat → Nat)
    (NR : Nat) : Bool :=
  allK NR (lookK CF NC JE LT RR RN LK)

@[expose] noncomputable def lookJK (CF : Nat → Nat → Nat) (NC JE JR JK : Nat → Nat) (NJ : Nat) :
    Bool :=
  allK NJ fun j => lookV CF NC (JE (JR j)) (JK j)

end CFSG.KC.Co2TInv

end
