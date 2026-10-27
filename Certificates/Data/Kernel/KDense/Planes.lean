module

public import CFSG.Certificates.Kernel.MonsterConv.Perm

public section

namespace CFSG.KC.KDense

open CFSG.KC CFSG.KC.MonsterConv.Perm CFSG.KC.Loop

@[expose] noncomputable def m4 (S : Nat) : Nat := ones (Nat.shiftLeft S (nat_lit 2))

@[expose] noncomputable def rep4 (S m : Nat) : Nat :=
  (fun m2 => Nat.lor m2 (Nat.shiftLeft m2 (Nat.shiftLeft S (nat_lit 1))))
    (Nat.lor m (Nat.shiftLeft m S))

@[expose] noncomputable def plane (S b x : Nat) : Nat :=
  Nat.land (Nat.shiftRight x (Nat.mul b S)) (ones S)

@[expose] noncomputable def negM (S m x : Nat) : Nat := Nat.xor x (rep4 S m)

@[expose] noncomputable def rotk (S k x : Nat) : Nat :=
  Nat.land (Nat.lor (Nat.shiftLeft x (Nat.mul k S))
    (Nat.shiftRight x (Nat.mul (Nat.sub (nat_lit 4) k) S))) (m4 S)

@[expose] noncomputable def add15 (S x y : Nat) : Nat :=
  (fun P G =>
    (fun G1 P1 =>
      (fun G2 => Nat.xor P (rotk S (nat_lit 1) G2))
        (Nat.lor G1 (Nat.land P1 (rotk S (nat_lit 2) G1))))
      (Nat.lor G (Nat.land P (rotk S (nat_lit 1) G))) (Nat.land P (rotk S (nat_lit 1) P)))
    (Nat.xor x y) (Nat.land x y)

@[expose] noncomputable def net4 (S k N x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun y => y)
    (fun j ih y => strictN
      ((fun i => dsw (stageShift k i) (rep4 S (Nat.land (Nat.shiftRight N (Nat.mul i S)) (ones S))) y)
        (Nat.sub (Nat.sub (Nat.mul (nat_lit 2) k) (nat_lit 2)) j)) ih)
    (Nat.sub (Nat.mul (nat_lit 2) k) (nat_lit 1)) x

@[expose] noncomputable def clr (S b : Nat) : Nat := Nat.xor (ones S) (idPlane S b)

@[expose] noncomputable def xsw (S b x : Nat) : Nat :=
  (fun d lo => Nat.lor (Nat.land (Nat.shiftRight x d) lo) (Nat.shiftLeft (Nat.land x lo) d))
    (Nat.shiftLeft (nat_lit 1) b) (rep4 S (clr S b))

@[expose] noncomputable def bfly (S b R x : Nat) : Nat :=
  (fun d lo =>
    (fun L U =>
      Nat.lor (Nat.land x (Nat.xor (m4 S) (rep4 S R)))
        (Nat.lor (add15 S L U) (Nat.shiftLeft (add15 S L (negM S lo U)) d)))
      (Nat.land x (rep4 S lo)) (Nat.land (Nat.shiftRight x d) (rep4 S lo)))
    (Nat.shiftLeft (nat_lit 1) b) (Nat.land R (clr S b))

@[expose] noncomputable def norm15 (S x : Nat) : Nat :=
  Nat.xor x (rep4 S (Nat.land (Nat.land (plane S (nat_lit 0) x) (plane S (nat_lit 1) x))
    (Nat.land (plane S (nat_lit 2) x) (plane S (nat_lit 3) x))))

end CFSG.KC.KDense

end
