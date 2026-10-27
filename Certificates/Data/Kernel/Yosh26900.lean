module

public import Certificates.Data.Kernel.Misc.PermClos

public section

namespace CFSG.KC.Yosh26900

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.Clos

@[expose] noncomputable def letN (y : Nat) (k : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (k (nat_lit 0)) (fun m _ => k (Nat.succ m)) y

@[expose] noncomputable def imW (s0 ec y l : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) y ec (Nat.beq l (nat_lit 1)))
    s0 (Nat.beq l (nat_lit 0))

@[expose] noncomputable def pathK (PA : Nat → Nat) (s0 ec y : Nat) (fuel : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => one (nat_lit 14))
    (fun _ ih k => Bool.rec (motive := fun _ => Nat)
      (letN (PA k) fun r => mul (nat_lit 14) (ih (Nat.land r (nat_lit 16777215)))
        (imW s0 ec y (Nat.shiftRight r (nat_lit 24))))
      (one (nat_lit 14)) (Nat.beq k (nat_lit 0))) fuel

@[expose] noncomputable def ord8 (y : Nat) : Bool :=
  letB (mul (nat_lit 14) y y) fun y2 => letB (mul (nat_lit 14) y2 y2) fun y4 =>
    andB (Nat.beq (mul (nat_lit 14) y4 y4) (one (nat_lit 14))) (notB (Nat.beq y4 (one (nat_lit 14))))

@[expose] noncomputable def fl (r a m : Nat) : Nat := Nat.land (Nat.shiftRight r a) m

@[expose] noncomputable def homAt (E PA : Nat → Nat) (s0 e ec g y k t m : Nat) : Bool :=
  andB (Nat.blt k (nat_lit 384)) (andB (Nat.blt t (nat_lit 3)) (andB (Nat.blt m (nat_lit 384))
    (andB (Nat.beq (E m) (mul (nat_lit 14) (E k) (imW s0 e g t)))
      (notB (Nat.beq (pathK PA s0 ec y (nat_lit 384) m)
        (mul (nat_lit 14) (pathK PA s0 ec y (nat_lit 384) k) (imW s0 ec y t)))))))

@[expose] noncomputable def clsAt (E PA CL SV : Nat → Nat) (s0 e ec g j : Nat) : Bool :=
  letB (CL j) fun r => letB (Nat.land r (nat_lit 3)) fun tag =>
    Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool)
          (Nat.beq (SV (fl r (nat_lit 2) (nat_lit 3))) j)
          (homAt E PA s0 e ec g (E j) (fl r (nat_lit 2) (nat_lit 511)) (fl r (nat_lit 11) (nat_lit 3))
            (fl r (nat_lit 13) (nat_lit 511)))
          (Nat.beq tag (nat_lit 2)))
        (notB (Nat.beq (pathK PA s0 ec (E j) (nat_lit 384) j) g))
        (Nat.beq tag (nat_lit 1)))
      (notB (ord8 (E j)))
      (Nat.beq tag (nat_lit 0))

@[expose] noncomputable def epsK (x : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) (Nat.beq (img x (nat_lit 12)) (nat_lit 13))

@[expose] noncomputable def lamK (x : Nat) : Nat := invs (nat_lit 4) x

@[expose] noncomputable def cenAt (E V : Nat → Nat) (c α k : Nat) : Bool :=
  letB (E k) fun x => Nat.beq (V k)
    (mul (nat_lit 14) x (pow (nat_lit 14) c (Nat.add (epsK x) (Nat.mul α (lamK x)))))

@[expose] noncomputable def ptAt (V TE TI PJ : Nat → Nat) (j : Nat) : Bool :=
  letB (PJ j) fun i => andB (Nat.blt i (nat_lit 128)) (Nat.beq (TE i) (V (TI j)))

@[expose] noncomputable def cntN (m : Nat) (f : Nat → Bool) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.add (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) (f i)) acc) m

@[expose] noncomputable def twB (u pu t : Nat) : Bool :=
  Nat.beq (mul (nat_lit 14) t pu) (mul (nat_lit 14) u t)

@[expose] noncomputable def bad4At (TE TI V : Nat → Nat) (u pu j : Nat) : Bool :=
  letB (TE j) fun t =>
    andB (impB (twB u u t) (Nat.beq (pow (nat_lit 14) t (nat_lit 4)) (one (nat_lit 14))))
      (impB (twB u pu t)
        (Nat.beq (pow (nat_lit 14) (mul (nat_lit 14) t (V (TI j))) (nat_lit 2)) (one (nat_lit 14))))

@[expose] noncomputable def badAt (TE TI V : Nat → Nat) (u pu : Nat) : Bool :=
  andB (Nat.beq (Nat.add (cntN (nat_lit 128) fun j => twB u u (TE j))
      (cntN (nat_lit 128) fun j => twB u pu (TE j))) (nat_lit 128))
    (allN (nat_lit 128) (bad4At TE TI V u pu))

@[expose] noncomputable def cnAt (E : Nat → Nat) (e c k : Nat) : Bool :=
  andB (comm (nat_lit 14) (E k) e) (comm (nat_lit 14) (E k) c)

@[expose] noncomputable def csAt (E : Nat → Nat) (s0 e c k : Nat) : Bool :=
  impB (comm (nat_lit 14) (E k) s0)
    (anyN (nat_lit 2) fun a => anyN (nat_lit 2) fun b => anyN (nat_lit 3) fun r =>
      Nat.beq (mul (nat_lit 14) (mul (nat_lit 14) (pow (nat_lit 14) e a) (pow (nat_lit 14) c b))
        (pow (nat_lit 14) s0 r)) (E k))

@[expose] noncomputable def sylAt (E SY : Nat → Nat) (s0 k : Nat) : Bool :=
  impB (andB (Nat.beq (pow (nat_lit 14) (E k) (nat_lit 3)) (one (nat_lit 14)))
      (notB (Nat.beq (E k) (one (nat_lit 14)))))
    (letB (SY k) fun h => andB (Nat.blt h (nat_lit 384))
      (orB (Nat.beq (mul (nat_lit 14) (E h) (E k)) (mul (nat_lit 14) s0 (E h)))
        (Nat.beq (mul (nat_lit 14) (E h) (E k)) (mul (nat_lit 14) (mul (nat_lit 14) s0 s0) (E h)))))

@[expose] noncomputable def vAt (PA V : Nat → Nat) (s0 ec y k : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (letB (PA k) fun r => letB (Nat.land r (nat_lit 16777215)) fun p =>
      andB (Nat.blt p k) (Nat.beq (V k) (mul (nat_lit 14) (V p)
        (imW s0 ec y (Nat.shiftRight r (nat_lit 24))))))
    (Nat.beq (V k) (one (nat_lit 14))) (Nat.beq k (nat_lit 0))

@[expose] noncomputable def wordF (A L : Nat → Nat) (m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (one (nat_lit 14)) (fun i acc => mul (nat_lit 14) acc (A (L i))) m

@[expose] noncomputable def tiAt (E TE TI : Nat → Nat) (j : Nat) : Bool :=
  andB (Nat.blt (TI j) (nat_lit 384)) (Nat.beq (E (TI j)) (TE j))

end CFSG.KC.Yosh26900

end
