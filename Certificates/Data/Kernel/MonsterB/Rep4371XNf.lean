module

public import Certificates.Data.Kernel.MonsterB.Rep4371X
public import CFSG.Certificates.Kernel.BabyMonster.PktCheck

public section

namespace CFSG.KC.Rep4371X

open CFSG.KC CFSG.KC.KDense CFSG.KC.Loop CFSG.KC.Rep4371Row CFSG.KC.BM.Pkt

@[expose] noncomputable def numT (c : Nat) : Int :=
  Bool.rec (motive := fun _ => Int) (Int.ofNat (nat_lit 0))
    (sgI (Nat.land c (nat_lit 1)) (Int.ofNat (Nat.shiftRight (nat_lit 8) (Nat.shiftRight c (nat_lit 1)))))
    (Nat.blt c (nat_lit 6))

@[expose] noncomputable def isZI (m : Int) : Bool :=
  Int.rec (motive := fun _ => Bool) (fun n => Nat.beq n (nat_lit 0)) (fun _ => false) m

@[expose] noncomputable def nilB (L : Terms) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) L

@[expose] noncomputable def insT (a : Nat) (m : Int) (L : Terms) : Terms :=
  List.rec (motive := fun _ => Terms) (List.cons (a, m) List.nil)
    (fun e rest ih => Bool.rec (motive := fun _ => Terms)
      (Bool.rec (motive := fun _ => Terms) (List.cons e ih)
        ((fun s => Bool.rec (motive := fun _ => Terms) (List.cons (a, s) rest) rest (isZI s))
          (Int.add m e.2))
        (Nat.beq a e.1))
      (List.cons (a, m) (List.cons e rest)) (Nat.blt a e.1)) L

@[expose] noncomputable def nfT (L : Terms) : Terms :=
  List.rec (motive := fun _ => Terms) List.nil (fun e _ ih => strictL e.1 fun a => insT a e.2 ih) L

@[expose] noncomputable def rowChk (f : Nat → Terms) (TH k : Nat) (R : Terms) : Bool :=
  nilB (nfT (appT (actVecT f (rawT TH k)) (scaleT (Int.negSucc (nat_lit 7)) (actVecT (rawT TH) R))))

@[expose] noncomputable def scStep (f : Nat → Terms) (TH : Nat) (st : Nat × Terms × Bool) (v : Nat) :
    Nat × Terms × Bool :=
  (fun t => Bool.rec (motive := fun _ => Nat × Terms × Bool) (st.1, List.cons t st.2.1, st.2.2)
      (Nat.succ st.1, List.nil, bAnd(st.2.2, rowChk f TH st.1 (List.cons t st.2.1)))
      (Nat.beq (Nat.div v (nat_lit 65536)) (nat_lit 1)))
    (Nat.mod v (nat_lit 8192), numT (Nat.mod (Nat.div v (nat_lit 8192)) (nat_lit 8)))

@[expose] noncomputable def scanR (f : Nat → Terms) (TH N i m : Nat) (st : Nat × Terms × Bool) :
    Nat × Terms × Bool :=
  Nat.rec (motive := fun _ => Nat × Terms × Bool) st
    (fun j ih => scStep f TH ih (entV N (Nat.add i j))) m

@[expose] noncomputable def chunkOK (f : Nat → Terms) (TH N i m k₀ k₁ : Nat) : Bool :=
  (fun st => bAnd(Nat.beq st.1 k₁, bAnd(nilB st.2.1, st.2.2)))
    (scanR f TH N i m (k₀, List.nil, true))

@[expose] noncomputable def lineChk (f : Nat → Terms) (TH : Nat) (p : Nat × Nat) : Bool :=
  chunkOK f TH p.1 (nat_lit 0) (Nat.div p.2 (nat_lit 3)) (nat_lit 0) (nat_lit 4371)

end CFSG.KC.Rep4371X

end
