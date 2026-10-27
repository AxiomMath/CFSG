module

public import Certificates.Data.Kernel.S5Ext.Check

public section

namespace CFSG.KD.S75Gen4

open CFSG.KD.S5Ext

@[expose] noncomputable def pt (P x : Nat) : Nat := Nat.land (Nat.shiftRight P (Nat.mul 4 x)) 15

@[expose] noncomputable def lP (n TAB i : Nat) : Nat :=
  Nat.land (Nat.shiftRight TAB (Nat.mul (Nat.mul 4 n) i)) (Nat.sub (Nat.shiftLeft 1 (Nat.mul 4 n)) 1)

@[expose] noncomputable def idC (n : Nat) : Nat :=
  Nat.rec 0 (fun x ih => Nat.lor ih (Nat.shiftLeft x (Nat.mul 4 x))) n

@[expose] noncomputable def compB (n P Q R : Nat) : Bool :=
  Nat.rec true (fun x ih => Bool.and ih (Nat.beq (pt R x) (pt P (pt Q x)))) n

@[expose] noncomputable def idB (n TAB : Nat) : Bool := Nat.beq (lP n TAB 0) (idC n)

@[expose] noncomputable def lanesB (n TAB : Nat) : Bool :=
  Bool.and (Nat.rec true (fun i ih => Bool.and ih
      (Nat.blt (lP n TAB (Nat.succ i)) (lP n TAB (Nat.succ (Nat.succ i))))) 126)
    (Nat.rec true (fun i ih => Bool.and ih
      (Bool.not (Nat.beq (lP n TAB (Nat.succ i)) (lP n TAB 0)))) 127)

@[expose] noncomputable def mpB (n TAB MP lo m : Nat) : Bool :=
  Nat.rec true (fun t ih => Bool.and ih ((fun g => Nat.rec true (fun c ih' => Bool.and ih'
    (compB n (lP n TAB g) (lP n TAB c) (lP n TAB (lM MP g c)))) 128) (Nat.add lo t))) m

@[expose] noncomputable def swapC (P a b : Nat) : Nat :=
  Nat.lor (Nat.sub P (Nat.lor (Nat.shiftLeft (pt P a) (Nat.mul 4 a)) (Nat.shiftLeft (pt P b) (Nat.mul 4 b))))
    (Nat.lor (Nat.shiftLeft (pt P b) (Nat.mul 4 a)) (Nat.shiftLeft (pt P a) (Nat.mul 4 b)))

@[expose] noncomputable def swC (n : Nat) (sw : List (Nat × Nat)) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun p _ ih acc => ih (swapC acc p.1 p.2)) sw (idC n)

@[expose] noncomputable def swB (n TAB : Nat) (GI : List Nat) (SW : List (List (Nat × Nat))) : Bool :=
  Bool.and (Nat.beq (lenL GI) SW.length)
    (List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
      (fun g _ ih k => Bool.and (Bool.and (Nat.blt g 128) (Nat.beq (lP n TAB g) (swC n (SW.getD k []))))
        (ih (Nat.succ k))) GI 0)

@[expose] noncomputable def treeG (MP : Nat) (GI : List Nat) (l : List (Nat × Nat × Nat)) :
    Nat → Bool × Nat :=
  List.rec (motive := fun _ => Nat → Bool × Nat) (fun seen => (true, seen))
    (fun r _ ih seen => (fun R => (Bool.and (Bool.and (Bool.and (tb seen r.2.1) (inL r.2.2 GI))
        (Nat.beq r.1 (lM MP r.2.1 r.2.2))) R.1, R.2)) (ih (Nat.lor seen (Nat.shiftLeft 1 r.1)))) l

@[expose] noncomputable def invB2 (MP INVP : Nat) : Bool :=
  Nat.rec true (fun g ih => Bool.and ih (Nat.beq (lM MP g (lI INVP g)) 0)) 128

@[expose] noncomputable def suppC (n P : Nat) : Nat :=
  Nat.rec 0 (fun x ih => Bool.rec (Nat.succ ih) ih (Nat.beq (pt P x) x)) n

@[expose] noncomputable def derB (MP : Nat) (gs : List Nat) (l : List (Nat × Nat × Nat)) :
    Nat → Bool × Nat :=
  List.rec (motive := fun _ => Nat → Bool × Nat) (fun seen => (true, seen))
    (fun r _ ih seen => (fun R => (Bool.and (Bool.and (Bool.and (tb seen r.2.1) (inL r.2.2 gs))
        (Nat.beq r.1 (lM MP r.2.1 r.2.2))) R.1, R.2)) (ih (Nat.lor seen (Nat.shiftLeft 1 r.1)))) l

@[expose] noncomputable def genRecB (n TAB MP C : Nat) (r : List Nat × List (Nat × Nat × Nat) × Nat) :
    Bool :=
  Bool.and (Bool.and (Nat.blt (lenL r.1) 5) (asOK C r.1))
    (Bool.and ((fun R => Bool.and R.1 (Nat.beq R.2 C)) (derB MP r.1 r.2.1 1))
      (Bool.rec true
        (Bool.and (Bool.and (tb C r.2.2) (Nat.beq (lM MP r.2.2 r.2.2) 0))
          (Bool.and (Nat.blt 0 r.2.2) (Nat.beq (suppC n (lP n TAB r.2.2)) 4)))
        (Nat.beq (lenL r.1) 4)))

@[expose] noncomputable def genRecsB (n TAB MP CATP : Nat) (k0 : Nat)
    (rs : List (List Nat × List (Nat × Nat × Nat) × Nat)) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun r _ ih k => Bool.and (genRecB n TAB MP (lC CATP k) r) (ih (Nat.succ k))) rs k0

end CFSG.KD.S75Gen4

end
