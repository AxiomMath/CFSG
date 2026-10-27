module

public import Certificates.Data.Kernel.CertF8.D48
public import Certificates.Data.Kernel.Misc.PermClos
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterD48SylowData

public section

namespace CFSG.KC.CertF8.S9640

open CFSG.KC.G28 (fld letN)
open CFSG.KC.CertF8 (mulS512)
open CFSG.KC.CertF8.D48 (letK oneK)
open CFSG.KC.Ord (andB orB)
open CFSG.KC.LQT.P (letB impB allN)
open CFSG.KC.Misc.Clos (treeAt sortAt closedAt)

@[expose] noncomputable def E (T : Nat → Nat) (j : Nat) : Nat := fld (T j) 0 576

@[expose] noncomputable def G (T : Nat → Nat) (l : Nat) : Nat := E T (Nat.add 729 l)

@[expose] noncomputable def PA (T : Nat → Nat) (k : Nat) : Nat :=
  Nat.add (fld (T k) 596 10) (Nat.mul 16777216 (fld (T k) 606 1))

@[expose] noncomputable def CT (T : Nat → Nat) (n : Nat) : Nat :=
  fld (T (Nat.div n 2)) (Nat.add 576 (Nat.mul 10 (Nat.mod n 2))) 10

@[expose] noncomputable def SG (T : Nat → Nat) (i : Nat) : Nat := fld (T i) 607 10

@[expose] noncomputable def cubeF (T : Nat → Nat) (j : Nat) : Bool := Nat.beq (fld (T j) 617 1) 1

@[expose] noncomputable def eqB (a b : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) true false b) b a

@[expose] noncomputable def cubeK (c : Nat) : Bool :=
  letB c fun c => Nat.beq (mulS512 c (mulS512 c c)) oneK

@[expose] noncomputable def memF (r o n j : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) false
    (fun t ih => orB (Nat.beq (fld r (Nat.add o (Nat.mul 10 t)) 10) j) ih) n

@[expose] noncomputable def conjAt (T : Nat → Nat) (j c : Nat) : Bool :=
  impB (cubeF T j) (orB (memF (T 739) 0 3 j)
    (letB (fld (T j) 618 10) fun g => letB (fld (T j) 628 3) fun q =>
      letB (fld (T (Nat.add 731 q)) 0 10) fun r => letB (E T g) fun eg =>
        andB (Nat.blt g 729) (andB (Nat.blt q 8)
          (Nat.beq (mulS512 eg c) (mulS512 (E T r) eg)))))

@[expose] noncomputable def rowAt (T : Nat → Nat) (j : Nat) : Bool :=
  andB (treeAt mulS512 oneK (G T) 2 (E T) (PA T) j)
    (andB (sortAt 729 (E T) (SG T) j)
      (andB (closedAt mulS512 (G T) 2 729 (E T) (CT T) j)
        (letB (E T j) fun c => andB (eqB (cubeF T j) (cubeK c)) (conjAt T j c))))

@[expose] noncomputable def repAt (T : Nat → Nat) (q j : Nat) : Bool :=
  letB (T (Nat.add 731 q)) fun rr => letB (fld rr 0 10) fun r =>
    andB (Nat.blt r 729) (impB (cubeF T j)
      (letB (E T j) fun c => letB (E T r) fun er =>
        impB (Nat.beq (mulS512 c er) (mulS512 er c)) (memF rr 10 9 j)))

@[expose] noncomputable def wordS (w : List Nat) : Nat :=
  w.foldr (fun l A => mulS512 (letK.getD l oneK) A) oneK

@[expose] noncomputable def powS (c : Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) oneK (fun _ acc => mulS512 c acc) n

@[expose] noncomputable def gensOK (T : Nat → Nat) : Bool :=
  andB (Nat.beq (G T 0) (wordS CFSG.AGLEmbedding.ChevOuterD48.sylowWordA))
    (Nat.beq (G T 1) (letN (wordS CFSG.AGLEmbedding.ChevOuterD48.sylowWordT) fun t => powS t 19))

end CFSG.KC.CertF8.S9640

end
