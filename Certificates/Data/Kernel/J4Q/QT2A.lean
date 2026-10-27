module

public import Certificates.Data.Kernel.J4Q.QT

public section

namespace CFSG.KC.J4Q

open CFSG.KC.Loop

@[expose] noncomputable def allR (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i ih => andB ih (f i)) n

@[expose] noncomputable def rowsJ (f : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft (f i) (Nat.mul (nat_lit 128) i))) (nat_lit 112)

@[expose] noncomputable def inWBK (rm P y : Nat) : Bool :=
  strictB (vecJ rm y P) fun v => allR (nat_lit 62) fun t => notB (bitB v (Nat.add (nat_lit 50) t))

@[expose] noncomputable def trivK (rm P : Nat) (cv : List Nat) (X : Nat) : Bool :=
  allR (nat_lit 12) fun j => inWBK rm P (Nat.xor (vecJ rm (getN (nat_lit 0) cv j) X) (getN (nat_lit 0) cv j))

@[expose] noncomputable def triK (ns ps : List Nat) : Bool :=
  andB (Nat.beq (List.length ns) (List.length ps)) (allR (List.length ns) fun k =>
    andB (Nat.blt (getN (nat_lit 0) ns k) (Nat.shiftLeft (nat_lit 1) (nat_lit 112)))
      (andB (Nat.blt (getN (nat_lit 0) ps k) (nat_lit 112))
        (andB (bitB (getN (nat_lit 0) ns k) (getN (nat_lit 0) ps k))
          (allR k fun j => notB (bitB (getN (nat_lit 0) ns k) (getN (nat_lit 0) ps j))))))

@[expose] noncomputable def vecEtaFrom (rm : Nat) (Ts : List Nat) (m : Nat) : Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ x => x)
    (fun T _ ih j x => Bool.rec (motive := fun _ => Nat) (ih (Nat.succ j) x)
      (strictN (vecJ rm x T) (ih (Nat.succ j)))
      (Nat.blt (nat_lit 0) (Nat.land m (Nat.shiftLeft (nat_lit 1) j)))) Ts

@[expose] noncomputable def vecEtaK (rm : Nat) (Ts : List Nat) (m x : Nat) : Nat :=
  vecEtaFrom rm Ts m (nat_lit 0) x

@[expose] noncomputable def pathVK (rm one : Nat) (Ms : List Nat) (p : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun l _ ih x => strictN (vecJ rm x (getN one Ms (Nat.sub l (nat_lit 1)))) ih) p

@[expose] noncomputable def eqLK (l₁ : List Nat) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun l₂ => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) l₂)
    (fun x _ ih l₂ => List.rec (motive := fun _ => Bool) false
      (fun y t _ => andB (Nat.beq x y) (ih t)) l₂) l₁

@[expose] noncomputable def pathRK (c rm one : Nat) (Ms : List Nat) (p : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) one
    (fun l _ ih => mulJ c rm (getN one Ms (Nat.sub l (nat_lit 1))) ih) p

end CFSG.KC.J4Q

end
