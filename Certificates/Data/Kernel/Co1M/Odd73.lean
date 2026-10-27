module

public import Certificates.Data.Kernel.Co1M.InvFam
public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.Odd73

open CFSG.KLie.CT CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KC.F2W CFSG.KC.InvFam CFSG.KC.SortTree

@[expose] def I73 : List Nat := [31, 35, 39, 43, 47, 51, 55, 59, 23, 17]

@[expose] def Ii73 : List Nat := [60, 61, 62, 63, 64, 65, 66, 67, 24, 25]

@[expose] def J73 : List Nat := [70, 73, 76, 86]

@[expose] noncomputable def act73 (R : List Nat) (l X : Nat) : Nat :=
  nIf(Nat.blt l (nat_lit 10), actC R I73 Ii73 l X,
    getL (nat_lit 0) R (getL (nat_lit 0) J73 (Nat.sub l (nat_lit 10))))

@[expose] noncomputable def clsA (a : Nat) : Nat := Nat.land a (nat_lit 7)

@[expose] noncomputable def ordA (a : Nat) : Nat := fld(a, nat_lit 3, nat_lit 255)

@[expose] noncomputable def preA (a c : Nat) : Nat :=
  fld(a, Nat.add (nat_lit 11) (Nat.mul (nat_lit 18) c), nat_lit 262143)

@[expose] noncomputable def preOK (a a' : Nat) : Bool :=
  allN (nat_lit 4) fun c => Nat.beq (preA a' c)
    (Nat.add (preA a c) (nIf(Nat.beq (clsA a) (Nat.add c (nat_lit 2)), nat_lit 1, nat_lit 0)))

@[expose] noncomputable def ruleOK (R : List Nat) (v L g c o cp : Nat) : Bool :=
  andB (Nat.blt c (nat_lit 6))
  (andB (bIf(Nat.beq L (nat_lit 0), Nat.beq c (nat_lit 1),
    bIf(Nat.blt g (nat_lit 8), Nat.beq c cp,
    bIf(Nat.blt g (nat_lit 10),
      bIf(Nat.beq cp (nat_lit 5), Nat.beq c (nat_lit 5),
        andB (Nat.beq c (nat_lit 0)) (andB (Nat.blt (nat_lit 0) o)
          (andB (Nat.beq (Nat.land o (nat_lit 1)) (nat_lit 0))
            (orderIsK (nat_lit 24) (mulW (nat_lit 24) (getL (nat_lit 0) R (nat_lit 27)) v) o)))),
    bIf(Nat.blt g (nat_lit 13), Nat.beq c (Nat.sub g (nat_lit 8)), Nat.beq c (nat_lit 5))))))
  (bIf(Nat.beq c (nat_lit 5),
    Nat.beq (mulW (nat_lit 24) v (getL (nat_lit 0) R (nat_lit 86)))
      (mulW (nat_lit 24) (getL (nat_lit 0) R (nat_lit 86)) v), true)))

@[expose] noncomputable def auxOK73 (R : List Nat) (rec aux : Nat → Nat) (wv wl wp i : Nat) :
    Bool :=
  (fun r => (fun a => andB (preOK a (aux (Nat.succ i)))
    (ruleOK R (valF wv r) (levF wv wl r) (letF wv wl wp r) (clsA a) (ordA a)
      (clsA (aux (parF wv wl wp r)))))
    (aux i)) (rec i)

@[expose] noncomputable def auxRun73 (R : List Nat) (rec aux : Nat → Nat) (wv wl wp lo m : Nat) :
    Bool :=
  allN m fun j => auxOK73 R rec aux wv wl wp (Nat.add lo j)

end CFSG.KC.Odd73

end
