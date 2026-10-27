module

public import Certificates.Data.Kernel.Spor.Fi24Kit
public import Certificates.Data.Kernel.Spor.Fi24FixP
public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.Fi24F4W

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.Fi24Net CFSG.KC.Fi24NetPt CFSG.KC.Fi24Kit
open CFSG.KC.Fi24FixP (fixS)
open CFSG.KC.Enum (allN strictB)

@[expose] noncomputable def rPt (NW : Nat → Nat → Nat) (NT : Nat → Nat) (cs : List Nat) (t : Bool)
    (x : Nat) : Nat :=
  wP NW cs (Bool.rec (motive := fun _ => Nat) x (ptF NT x) t)

@[expose] noncomputable def rPl (NW : Nat → Nat → Nat) (NT : Nat → Nat) (cs : List Nat) (t : Bool)
    (v : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (walkP NW cs v) (netF NT (walkP NW cs v)) t

@[expose] noncomputable def bitsL (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x _ ih => Nat.lor (Nat.shiftLeft (nat_lit 1) x) ih) l

@[expose] noncomputable def coverOK (NW : Nat → Nat → Nat) (NT : Nat → Nat) (cs : List Nat)
    (t : Bool) (prods : List (List Nat)) (q₀ : Nat) (E : List Nat) : Bool :=
  letB (List.rec (motive := fun _ => Nat) (fixS (rPl NW NT cs t))
      (fun c _ ih => Nat.land (fixS (walkP NW c)) ih) prods) (fun A =>
    Nat.beq (Nat.land A (bitsL (q₀ :: E))) A)

@[expose] noncomputable def allLN (l : List Nat) (f : Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => andB (f x) ih) l

@[expose] noncomputable def prodOK (NW : Nat → Nat → Nat) (OL NT : Nat → Nat) (B c : List Nat)
    (q q₀ : Nat) : Bool :=
  allLN B (fun b => Nat.beq (wP NW c b) (clsK OL NT q (clsK OL NT q₀ b)))

@[expose] noncomputable def commQ (OL NT : Nat → Nat) (a b : Nat) : Bool :=
  Nat.beq (clsK OL NT a b) b

@[expose] noncomputable def witOK (OL NT : Nat → Nat) (q₀ p q x : Nat) : Bool :=
  letB (clsK OL NT q (clsK OL NT q₀ (clsK OL NT p x))) (fun y =>
    Bool.not (Nat.beq (clsK OL NT q (clsK OL NT q₀ (clsK OL NT p y))) x))

@[expose] noncomputable def qfixOK (NW : Nat → Nat → Nat) (NT : Nat → Nat) (cs : List Nat) (t : Bool)
    (Q : List Nat) : Bool :=
  allLN Q (fun q => Nat.beq (rPt NW NT cs t q) q)

@[expose] noncomputable def nthN (l : List Nat) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun x _ ih i => Nat.rec (motive := fun _ => Nat) x (fun j _ => ih j) i) l i

@[expose] noncomputable def nthL (l : List (List Nat)) (i : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun x _ ih i => Nat.rec (motive := fun _ => List Nat) x (fun j _ => ih j) i) l i

@[expose] noncomputable def graphOK (OL NT : Nat → Nat) (Q par : List Nat) (th : List (List Nat))
    (m : Nat) : Bool :=
  andB (allN m (fun j => orB (Nat.beq j (nat_lit 0)) (andB (Nat.blt (nthN par j) j)
      (Bool.not (commQ OL NT (nthN Q (nthN par j)) (nthN Q j))))))
    (allN m (fun i => allN m (fun j => strictB (nthN (nthL th i) j) (fun k =>
      bIf(Nat.beq k (nat_lit 0), commQ OL NT (nthN Q i) (nthN Q j),
        andB (Nat.blt (Nat.sub k (nat_lit 1)) m)
          (andB (commQ OL NT (nthN Q (Nat.sub k (nat_lit 1))) (nthN Q i))
            (commQ OL NT (nthN Q (Nat.sub k (nat_lit 1))) (nthN Q j))))))))

end CFSG.KC.Fi24F4W

end
