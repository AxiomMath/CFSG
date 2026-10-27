module

public import Certificates.Data.Kernel.LocalQT.Lat

public section

namespace CFSG.KC.F48S

open CFSG.KC.Ord CFSG.KC.LQT.L

@[expose] noncomputable def encL (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun a _ ih => Nat.add a (Nat.shiftLeft ih (nat_lit 6))) l

@[expose] noncomputable def pget (p j : Nat) : Nat :=
  Nat.land (Nat.shiftRight p (Nat.mul (nat_lit 6) j)) (nat_lit 63)

@[expose] noncomputable def pcomp (p : Nat) (k : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun _ ih q => Nat.add (pget p (Nat.land q (nat_lit 63)))
      (Nat.shiftLeft (ih (Nat.shiftRight q (nat_lit 6))) (nat_lit 6))) k

@[expose] noncomputable def eqAt (p q r s : Nat) (n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun i ih => andB (Nat.beq (pget p (pget q i)) (pget r (pget s i))) ih) n

@[expose] noncomputable def getK (l : List Nat) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun x _ ih j => Bool.rec (motive := fun _ => Nat) (ih (Nat.sub j 1)) x (Nat.beq j 0)) l i

@[expose] noncomputable def setT (l : List Nat) : NT :=
  List.rec (motive := fun _ => NT) NT.lf (fun x _ ih => insT ih x) l

@[expose] noncomputable def letK {n : Nat} (LP LPi : List Nat) (l : Fin n × Bool) : Nat :=
  getK (Bool.rec (motive := fun _ => List Nat) LPi LP l.2) l.1

@[expose] noncomputable def evFrom {n : Nat} (N : Nat) (LP LPi : List Nat) (w : List (Fin n × Bool)) :
    Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun l _ ih acc => ih (pcomp acc N (letK LP LPi l))) w

@[expose] noncomputable def evK {n : Nat} (N : Nat) (LP LPi : List Nat) (w : List (Fin n × Bool)) :
    Nat :=
  evFrom N LP LPi w (encL (List.range N))

@[expose] noncomputable def normK (N : Nat) (KP : List Nat) (x : Nat) : Bool :=
  allA KP fun k => anyA KP fun k' => eqAt x k k' x N

@[expose] noncomputable def closedK (N : Nat) (T : NT) (LP GP : List Nat) : Bool :=
  allA LP fun x => allA GP fun g => memT T (pcomp x N g)

@[expose] noncomputable def uvwK (UP VP WP : List Nat) (m : Nat) : List (Nat × Nat × Nat) :=
  (List.range m).map fun k => (getK UP k, getK VP k, getK WP k)

@[expose] noncomputable def candK (N : Nat) (T1 T2 : NT) (P1P P2P KP TP : List Nat)
    (UVW : List (Nat × Nat × Nat)) : Bool :=
  allA P1P fun x =>
    orB (notB (normK N KP x)) (orB (notB (memT (setT KP) (pcomp x N x))) (orB (memT T2 x)
      (allA P2P fun y =>
        orB (notB (normK N KP y)) (orB (notB (memT (setT KP) (pcomp y N y))) (orB (memT T1 y)
          (allA KP fun c => anyA TP fun t => anyA UVW fun p =>
            andB (eqAt t x p.1 t N) (andB (eqAt t y p.2.1 t N) (eqAt t c p.2.2 t N))))))))

end CFSG.KC.F48S
