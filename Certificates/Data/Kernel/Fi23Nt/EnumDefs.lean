module

public import Certificates.Data.Kernel.Fi23K.Defs

public section

namespace CFSG.KC.Fi23Nt

open CFSG.KC.Enum CFSG.KC.Fi23K

@[expose] noncomputable def lnK (w P i : Nat) : Nat :=
  Nat.land (Nat.shiftRight P (Nat.mul w i)) (Nat.sub (Nat.shiftLeft (nat_lit 1) w) (nat_lit 1))

@[expose] noncomputable def ptK (c t : Nat) : Nat := lnK (nat_lit 15) c t

@[expose] noncomputable def mk6K (a0 a1 a2 a3 a4 a5 : Nat) : Nat :=
  Nat.lor a0 (Nat.lor (Nat.shiftLeft a1 (nat_lit 15)) (Nat.lor (Nat.shiftLeft a2 (nat_lit 30))
    (Nat.lor (Nat.shiftLeft a3 (nat_lit 45)) (Nat.lor (Nat.shiftLeft a4 (nat_lit 60))
      (Nat.shiftLeft a5 (nat_lit 75))))))

@[expose] noncomputable def actK (G : Nat → Nat) (w : List Nat) (c : Nat) : Nat :=
  strictN (wv G w (ptK c (nat_lit 0))) fun a0 => strictN (wv G w (ptK c (nat_lit 1))) fun a1 =>
    strictN (wv G w (ptK c (nat_lit 2))) fun a2 => strictN (wv G w (ptK c (nat_lit 3))) fun a3 =>
      strictN (wv G w (ptK c (nat_lit 4))) fun a4 => strictN (wv G w (ptK c (nat_lit 5))) fun a5 =>
        mk6K a0 a1 a2 a3 a4 a5

@[expose] noncomputable def cdK (IMG i : Nat) : Nat := lnK (nat_lit 96) IMG i

@[expose] noncomputable def ltK (LT : List Nat) (j i : Nat) : Nat :=
  lnK (nat_lit 16) (List.getD LT j (nat_lit 0)) i

@[expose] noncomputable def enumIK (G : Nat → Nat) (W : List (List Nat)) (m n PAR IMG : Nat)
    (LT : List Nat) (i : Nat) : Bool :=
  bAnd(bIf(Nat.beq i (nat_lit 0),
      Nat.beq (cdK IMG (nat_lit 0)) (mk6K (nat_lit 0) (nat_lit 1) (nat_lit 2) (nat_lit 3)
        (nat_lit 4) (nat_lit 5)),
      strictB (lnK (nat_lit 16) PAR i) fun q =>
        strictB (Nat.shiftRight q (nat_lit 2)) fun p => strictB (Nat.land q (nat_lit 3)) fun j =>
          bAnd(Nat.blt p i, bAnd(Nat.blt j m, Nat.beq (ltK LT j p) i))),
    strictB (cdK IMG i) fun c =>
      allN m fun j => strictB (ltK LT j i) fun k =>
        bAnd(Nat.blt k n, Nat.beq (cdK IMG k) (actK G (List.getD W j []) c)))

@[expose] noncomputable def enumSlK (G : Nat → Nat) (W : List (List Nat)) (m n PAR IMG : Nat)
    (LT : List Nat) (lo len : Nat) : Bool :=
  allBlk lo (enumIK G W m n PAR IMG LT) len

@[expose] noncomputable def ordK (IMG ORD n : Nat) : Bool :=
  bAnd(Nat.blt (lnK (nat_lit 16) ORD (Nat.pred n)) n,
    allN (Nat.pred n) fun k => strictB (lnK (nat_lit 16) ORD k) fun a =>
      bAnd(Nat.blt a n, Nat.blt (cdK IMG a) (cdK IMG (lnK (nat_lit 16) ORD (Nat.succ k)))))

end CFSG.KC.Fi23Nt

end
