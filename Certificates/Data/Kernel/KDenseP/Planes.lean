module

public import CFSG.Certificates.Kernel.MonsterConv.Perm

public section

namespace CFSG.KC.KDenseP

open CFSG.KC CFSG.KC.MonsterConv.Perm CFSG.KC.Loop

@[expose] noncomputable def mN (S n : Nat) : Nat := ones (Nat.mul n S)

@[expose] noncomputable def repN (S n m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun b acc => Nat.lor acc (Nat.shiftLeft m (Nat.mul b S))) n

@[expose] noncomputable def planeN (S b x : Nat) : Nat :=
  Nat.land (Nat.shiftRight x (Nat.mul b S)) (ones S)

@[expose] noncomputable def negMN (S n m x : Nat) : Nat := Nat.xor x (repN S n m)

@[expose] noncomputable def rotN (S n k x : Nat) : Nat :=
  Nat.land (Nat.lor (Nat.shiftLeft x (Nat.mul k S))
    (Nat.shiftRight x (Nat.mul (Nat.sub n k) S))) (mN S n)

@[expose] noncomputable def dvN (n j : Nat) : Nat := Nat.mod (Nat.mul (Nat.sub n (nat_lit 1)) j) n

@[expose] noncomputable def strictNP (y : Nat) (k : Nat → Nat × Nat) : Nat × Nat :=
  Nat.rec (motive := fun _ => Nat × Nat) (k (nat_lit 0)) (fun m _ => k (Nat.succ m)) y

@[expose] noncomputable def addN (S n lg x y : Nat) : Nat :=
  (fun P0 G0 =>
    Prod.rec (motive := fun _ => Nat) (fun G _ => Nat.xor P0 (rotN S n (Nat.mod (nat_lit 1) n) G))
      (Nat.rec (motive := fun _ => Nat × Nat) (G0, P0)
        (fun i ih => Prod.rec (motive := fun _ => Nat × Nat)
          (fun G P => (fun s => strictNP (Nat.lor G (Nat.land P (rotN S n s G)))
              (fun G' => (G', Nat.land P (rotN S n s P))))
            (Nat.mod (Nat.shiftLeft (nat_lit 1) i) n)) ih) lg))
    (Nat.xor x y) (Nat.land x y)

@[expose] noncomputable def netN (S n k N x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun y => y)
    (fun j ih y => strictN
      ((fun i => dsw (stageShift k i) (repN S n (Nat.land (Nat.shiftRight N (Nat.mul i S)) (ones S))) y)
        (Nat.sub (Nat.sub (Nat.mul (nat_lit 2) k) (nat_lit 2)) j)) ih)
    (Nat.sub (Nat.mul (nat_lit 2) k) (nat_lit 1)) x

@[expose] noncomputable def clrN (S b : Nat) : Nat := Nat.xor (ones S) (idPlane S b)

@[expose] noncomputable def xswN (S n b x : Nat) : Nat :=
  (fun d lo => Nat.lor (Nat.land (Nat.shiftRight x d) lo) (Nat.shiftLeft (Nat.land x lo) d))
    (Nat.shiftLeft (nat_lit 1) b) (repN S n (clrN S b))

@[expose] noncomputable def bflyN (S n lg b R x : Nat) : Nat :=
  (fun d lo =>
    (fun L U =>
      Nat.lor (Nat.land x (Nat.xor (mN S n) (repN S n R)))
        (Nat.lor (addN S n lg L U) (Nat.shiftLeft (addN S n lg L (negMN S n lo U)) d)))
      (Nat.land x (repN S n lo)) (Nat.land (Nat.shiftRight x d) (repN S n lo)))
    (Nat.shiftLeft (nat_lit 1) b) (Nat.land R (clrN S b))

@[expose] noncomputable def normN (S n x : Nat) : Nat :=
  Nat.xor x (repN S n (Nat.rec (motive := fun _ => Nat) (ones S)
    (fun b acc => Nat.land acc (planeN S b x)) n))

end CFSG.KC.KDenseP

end
