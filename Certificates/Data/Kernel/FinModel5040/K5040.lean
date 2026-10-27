module

public import Certificates.Data.Kernel.Misc.A7Nat

public section

namespace CFSG.KD.FM5040

open CFSG.KC.LQT.P CFSG.KC.Ord CFSG.KD.A7Nat

@[expose] noncomputable def movK (m s : Nat) : Nat := Nat.sub m (fix m s)

@[expose] noncomputable def invoK (m s : Nat) : Bool :=
  andB (Nat.beq (mul m s s) (one m)) (notB (Nat.beq s (one m)))

@[expose] noncomputable def exK (m : Nat) (R : List Nat) (s : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 4) (movK m s) (memL s R)

@[expose] noncomputable def baseK (m a : Nat) (R : List Nat) : Bool :=
  andB (Nat.beq (mul m a a) (one m)) (andB (notB (memL a R))
    (allL R fun p => memL (mul m (mul m a p) (inv m a)) R))

@[expose] noncomputable def oddK (m a : Nat) (R : List Nat) : Bool :=
  allL R fun p => letB (mul m p a) fun q =>
    impB (Nat.beq (mul m q q) (one m))
      (andB (impB (notB (Nat.beq q (one m))) (Nat.beq (movK m q) (nat_lit 8)))
        (anyL R fun r => Nat.beq (mul m (mul m r a) (inv m r)) q))

@[expose] noncomputable def centK (m a x : Nat) (S : List Nat) : Bool :=
  allL S fun y => impB (invoK m y)
    (impB (Nat.beq (cntL (comm m y) S) (nat_lit 64))
      (orB (Nat.beq y x) (Nat.beq y (conj m a x))))

@[expose] noncomputable def pairK (m x y1 y2 : Nat) : Bool :=
  orB (notB (Nat.beq (movK m y2) (nat_lit 4)))
    (orB (notB (Nat.beq (movK m (mul m x y1)) (nat_lit 4)))
      (letB (mul m y1 y2) fun z => notB (Nat.beq (movK m (mul m z z)) (nat_lit 8))))

@[expose] noncomputable def etaK (m a x g1 g2 : Nat) (R C : List Nat) : Bool :=
  andB (andB (memL a C) (andB (memL g1 C) (memL g2 C)))
    (andB (letB (mul m g1 g2) fun z => letB (mul m z z) fun u =>
        andB (invoK m u) (Nat.beq (exK m R u) (nat_lit 8)))
      (andB (andB (invoK m g2) (Nat.beq (exK m R g2) (nat_lit 4)))
        (andB (letB (mul m a g1) fun u => andB (invoK m u) (Nat.beq (exK m R u) (nat_lit 4)))
          (allL R fun y1 => allL R fun y2 => pairK m x y1 y2))))

@[expose] noncomputable def allK (m : Nat) (M R S C : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a t _ =>
    List.rec (motive := fun _ => Bool) false (fun x t2 _ =>
      List.rec (motive := fun _ => Bool) false (fun g1 t3 _ =>
        List.rec (motive := fun _ => Bool) false (fun g2 _ _ =>
          andB (baseK m a R) (andB (oddK m a R) (andB (nodupL S)
            (andB (centK m a x S) (etaK m a x g1 g2 R C))))) t3) t2) t) M

end CFSG.KD.FM5040

end
