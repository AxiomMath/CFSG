module

public import Certificates.Data.Kernel.SporCov.Defs

public section

namespace CFSG.KC.SporCov

@[expose] noncomputable def nthN (l : List Nat) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun a _ ih j => Nat.rec (motive := fun _ => Nat) a (fun k _ => ih k) j) l i

@[expose] noncomputable def lenN (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => ih + 1) l

@[expose] noncomputable def lenW (W : List (List Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => ih + 1) W

@[expose] noncomputable def dig (p m t : Nat) : Nat :=
  m / p ^ t % p

@[expose] noncomputable def nfW (H : List (List Nat)) (e : Nat → Nat) (n : Nat) : Nat → List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun _ ih i => ih (i + 1) ++ repW (nthW H i) (e i)) n

@[expose] noncomputable def cw (H : List (List Nat)) (k p m : Nat) : List Nat :=
  nfW H (dig p m) k 0

@[expose] noncomputable def zeroTo (e : Nat → Nat) (i : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun t ih => Nat.beq (e t) 0 && ih) (i + 1)

@[expose] noncomputable def pcR (E : List Nat → List Nat → Bool) (p : Nat) (H R : List (List Nat))
    (k i j : Nat) : Bool :=
  zeroTo (nthN (nthW R (i * k + j))) i &&
    cond (Nat.beq i j)
      (E (repW (nthW H i) p) (nfW H (nthN (nthW R (i * k + j))) k 0))
      (E (nthW H i ++ nthW H j) (nfW H (nthN (nthW R (i * k + j))) k 0 ++ nthW H i))

@[expose] noncomputable def neA (E : List Nat → List Nat → Bool) (W : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun w _ ih => neOK E w && ih) W

@[expose] noncomputable def cenH (E : List Nat → List Nat → Bool) (L : Nat → Bool)
    (H Rp Gs : List (List Nat)) (P : List Nat) (N : Nat) : Bool :=
  chA L H && chA L Rp && chA L Gs && neA E Rp && Nat.beq (lenN P) N

@[expose] noncomputable def keyFrom (K : List Nat → Nat) (H : List (List Nat)) (k p : Nat)
    (P : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun m _ ih prev => (fun x => Nat.blt prev x && ih x) (K (cw H k p m))) P

@[expose] noncomputable def keyInc (K : List Nat → Nat) (H : List (List Nat)) (k p : Nat)
    (P : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun m P' _ => keyFrom K H k p P' (K (cw H k p m))) P

@[expose] noncomputable def cenOK (E : List Nat → List Nat → Bool) (p : Nat) (H : List (List Nat))
    (k : Nat) (Rp Gs : List (List Nat)) (P : List Nat) (T : List (List Nat)) (N n : Nat) :
    Bool :=
  cond (Nat.beq (nthN (nthW T n) 0) 0) (E (cw H k p (nthN P n)) [])
    (cond (Nat.beq (nthN (nthW T n) 0) 1) (neOK E (repW (cw H k p (nthN P n)) p))
      (cond (Nat.beq (nthN (nthW T n) 0) 2)
        (Nat.blt (nthN (nthW T n) 1) (lenW Rp) &&
          cjOK E (nthW Rp (nthN (nthW T n) 1)) (nthW Gs (nthN (nthW T n) 2)) (cw H k p (nthN P n)))
        (cond (Nat.beq (nthN (nthW T n) 0) 3)
          (Nat.blt (nthN (nthW T n) 1) N &&
            Nat.beq (nthN (nthW T (nthN (nthW T n) 1)) 0) 2 &&
            E (repW (cw H k p (nthN P n)) (nthN (nthW T n) 2))
              (cw H k p (nthN P (nthN (nthW T n) 1))))
          false)))

end CFSG.KC.SporCov

end
