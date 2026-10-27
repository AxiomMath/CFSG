module

public import Certificates.Data.Kernel.BabyMonster.CTIB.CosetQ
public import Certificates.Data.Kernel.M1F2

public section

namespace CFSG.KC.BM.OrbW

open CFSG.KC.BM CFSG.KC.BM.CosetQ

@[expose] noncomputable def fldB (w B : Nat) (L : List Nat) (i : Nat) : Nat :=
  Nat.land (Nat.shiftRight (nthN L (Nat.div i B)) (Nat.mul w (Nat.mod i B)))
    (Nat.sub (Nat.shiftLeft (nat_lit 1) w) (nat_lit 1))

@[expose] noncomputable def ptB (B : Nat) (SB : List Nat) (i : Nat) : Nat := fldB (nat_lit 32) B SB i

@[expose] noncomputable def imgB (B ngen : Nat) (EB : List Nat) (i k : Nat) : Nat :=
  Nat.land (Nat.shiftRight (nthN EB (Nat.div i B))
    (Nat.mul (nat_lit 16) (Nat.add (Nat.mul ngen (Nat.mod i B)) k))) (nat_lit 65535)

@[expose] noncomputable def tPar (t : Nat) : Nat := Nat.land t (nat_lit 65535)

@[expose] noncomputable def tLab (t : Nat) : Nat := Nat.land (Nat.shiftRight t (nat_lit 16)) (nat_lit 63)

@[expose] noncomputable def tDep (t : Nat) : Nat := Nat.shiftRight t (nat_lit 22)

@[expose] noncomputable def incB (B n bound : Nat) (SB : List Nat) (i : Nat) : Bool :=
  (fun p => andB (Nat.blt p bound)
    (Bool.rec (motive := fun _ => Bool) true (Nat.blt p (ptB B SB (Nat.succ i)))
      (Nat.blt (Nat.succ i) n))) (ptB B SB i)

@[expose] noncomputable def closB (act : Nat → Nat → Nat) (ngen B n : Nat) (SB EB : List Nat)
    (i : Nat) : Bool :=
  (fun p => allLt ngen fun k => (fun j => andB (Nat.blt j n) (Nat.beq (act k p) (ptB B SB j)))
    (imgB B ngen EB i k)) (ptB B SB i)

@[expose] noncomputable def edgeB (act : Nat → Nat → Nat) (ngen B n : Nat) (SB TB : List Nat)
    (i t : Nat) : Bool :=
  andB (Nat.blt (tPar t) n) (andB (Nat.blt (tLab t) ngen)
    (andB (Nat.beq (Nat.succ (tDep (ptB B TB (tPar t)))) (tDep t))
      (Nat.beq (act (tLab t) (ptB B SB (tPar t))) (ptB B SB i))))

@[expose] noncomputable def treeB (act : Nat → Nat → Nat) (ngen B n r : Nat) (SB TB : List Nat)
    (i : Nat) : Bool :=
  (fun t => Bool.rec (motive := fun _ => Bool) (edgeB act ngen B n SB TB i t)
    (Nat.beq (tDep t) (nat_lit 0)) (Nat.beq i r)) (ptB B TB i)

@[expose] noncomputable def cjAutK (LO : Nat) (Gs EC : List Nat) (j n : Nat) : Nat :=
  (fun e => mulQ LO (mulQ LO e (autQ LO (nthN Gs j) n)) e) (nthN EC j)

@[expose] noncomputable def walkC (P1 P2 w len v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) v (fun i acc => CFSG.KC.M1F2.vmF (nat_lit 22)
    (Bool.rec (motive := fun _ => Nat) P1 P2
      (Nat.beq (Nat.land (Nat.shiftRight w i) (nat_lit 1)) (nat_lit 1))) acc) len

@[expose] noncomputable def eRecC (e : Nat) : Nat := Nat.land (Nat.shiftRight e (nat_lit 22)) (nat_lit 7)

@[expose] noncomputable def walkE (P1 P2 e : Nat) : Bool :=
  andB (Nat.blt (eRecC e) (nat_lit 5))
    (Nat.beq (walkC P1 P2 (Nat.shiftRight e (nat_lit 31))
      (Nat.land (Nat.shiftRight e (nat_lit 25)) (nat_lit 63))
      (nthN [nat_lit 1, nat_lit 3, nat_lit 7, nat_lit 17, nat_lit 19] (eRecC e)))
      (Nat.land e (nat_lit 4194303)))

@[expose] noncomputable def frChk (LO AH R c P1 P2 a e : Nat) : Nat :=
  (fun n => (fun v => Bool.rec (motive := fun _ => Nat) (nat_lit 1)
      (Bool.rec (motive := fun _ => Nat)
        (Bool.rec (motive := fun _ => Nat) (nat_lit 0)
          (Bool.rec (motive := fun _ => Nat) (nat_lit 1) (nat_lit 2) (Nat.beq (eRecC e) (nat_lit 2)))
          (andB (walkE P1 P2 e) (Nat.beq (Nat.land e (nat_lit 4194303)) v)))
        (nat_lit 1) (Nat.beq v (nat_lit 0)))
      (Nat.beq (mulQ LO (autQ LO AH n) c) (mulQ LO c n)))
    (Nat.land n (nat_lit 4194303))) (mulQ LO R a)

@[expose] noncomputable def cntB (f : Nat → Nat) (lo len : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun j acc => Nat.add acc (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1)
      (Nat.beq (f (Nat.add lo j)) (nat_lit 2)))) len

@[expose] noncomputable def okB (f : Nat → Nat) (lo len : Nat) : Bool :=
  allLt len fun j => notB (Nat.beq (f (Nat.add lo j)) (nat_lit 0))

end CFSG.KC.BM.OrbW

end
