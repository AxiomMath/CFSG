module

public import Certificates.Data.Kernel.Spor.Prim

public section

namespace CFSG.KC.Over77

open CFSG.KC.Enum CFSG.KS.Prim

@[expose] noncomputable def cp (p q : Nat) : Nat := pcomp (nat_lit 77) (nat_lit 7) (nat_lit 127) p q

@[expose] noncomputable def canon (p : Nat) : Bool :=
  canonK (nat_lit 77) (nat_lit 7) (nat_lit 127) (nat_lit 539) p

@[expose] noncomputable def idK (x : Nat) : Bool := Nat.beq x (pidn (nat_lit 77) (nat_lit 7))

@[expose] noncomputable def nth (L : List Nat) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun x _ ih i => Nat.rec (motive := fun _ => Nat) x (fun j _ => ih j) i) L i

@[expose] noncomputable def let4 (A B Z Y c : Nat) : Nat :=
  nIf(Nat.beq c (nat_lit 0), A, nIf(Nat.beq c (nat_lit 1), B, nIf(Nat.beq c (nat_lit 2), Z, Y)))

@[expose] noncomputable def wordV (g : Nat → Nat) (len W : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => pidn (nat_lit 77) (nat_lit 7))
    (fun _ ih W => strictN (ih (Nat.shiftRight W (nat_lit 2))) (fun v =>
      cp (g (Nat.land W (nat_lit 3))) v)) len W

@[expose] noncomputable def mulK (T P S : Nat → Nat) (i D : Nat) : Bool :=
  allBlk (nat_lit 0) (fun l => strictB (T (Nat.add (Nat.shiftLeft i (nat_lit 3)) l)) (fun t =>
    allBlk (nat_lit 0) (fun k =>
      strictB (fld(D, Nat.mul (nat_lit 20) (Nat.add (Nat.mul (nat_lit 9) l) k), nat_lit 1048575))
        (fun r => strictB (fld(r, nat_lit 0, nat_lit 127)) (fun p =>
          strictB (fld(r, nat_lit 7, nat_lit 8191)) (fun j' =>
            bAnd(Nat.blt p (nat_lit 110), bAnd(Nat.blt j' (nat_lit 8064),
              Nat.beq (cp t (S k)) (cp (P p) (T j')))))))) (nat_lit 9))) (nat_lit 8)

@[expose] noncomputable def clsK (T P X : Nat → Nat) (i D : Nat) : Bool :=
  allBlk (nat_lit 0) (fun l => strictB (T (Nat.add (Nat.shiftLeft i (nat_lit 5)) l)) (fun t =>
    strictB (fld(D, Nat.mul (nat_lit 21) l, nat_lit 2097151)) (fun r =>
      strictB (fld(r, nat_lit 0, nat_lit 127)) (fun c =>
        strictB (fld(r, nat_lit 7, nat_lit 127)) (fun p =>
          strictB (fld(r, nat_lit 14, nat_lit 127)) (fun q =>
            bAnd(canon t, bAnd(Nat.blt p (nat_lit 110),
              bIf(Nat.beq c (nat_lit 0), Nat.beq t (P p),
                bAnd(Nat.blt c (nat_lit 83), bAnd(Nat.blt q (nat_lit 110),
                  Nat.beq t (cp (cp (P p) (X (Nat.sub c (nat_lit 1)))) (P q))))))))))))) (nat_lit 32)

@[expose] noncomputable def pwK (A B Z : Nat) (P : Nat → Nat) (p len W : Nat) : Bool :=
  Nat.beq (P p) (wordV (let4 A B Z (pidn (nat_lit 77) (nat_lit 7))) len W)

@[expose] noncomputable def swK (A B Z : Nat) (X : Nat → Nat) (σ i len W : Nat) : Bool :=
  strictB (X i) (fun x => bAnd(canon x, Nat.beq (wordV (let4 A B Z x) len W) σ))

end CFSG.KC.Over77

end
