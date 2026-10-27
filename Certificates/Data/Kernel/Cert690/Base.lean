module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.C690

open CFSG.KC.Enum

@[expose] noncomputable def rep6 : Nat := nat_lit 1090785345

@[expose] noncomputable def mtF (a b k : Nat) : Nat :=
  Nat.land (Nat.mul (Nat.land (Nat.shiftRight a (Nat.mul (nat_lit 6) k)) (nat_lit 63)) rep6)
    (Nat.mul (Nat.land (Nat.shiftRight b k) rep6) (nat_lit 63))

@[expose] noncomputable def mulF (a b : Nat) : Nat :=
  Nat.xor (Nat.xor (Nat.xor (mtF a b (nat_lit 0)) (mtF a b (nat_lit 1)))
      (Nat.xor (mtF a b (nat_lit 2)) (mtF a b (nat_lit 3))))
    (Nat.xor (mtF a b (nat_lit 4)) (mtF a b (nat_lit 5)))

@[expose] noncomputable def oneF : Nat := nat_lit 34630287489

@[expose] noncomputable def ifN (c : Bool) (t e : Nat) : Nat := Bool.rec (motive := fun _ => Nat) e t c

@[expose] noncomputable def andK (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) false b a

@[expose] noncomputable def invStep (x : Nat) (k : Nat → Nat) (y : Nat) : Nat :=
  ifN (Nat.beq (mulF y x) oneF) y (k (mulF y x))

@[expose] noncomputable def invGo (x : Nat) (fuel : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun y => y) (fun _ ih y => invStep x ih y) fuel

inductive IT where
  | leaf : IT
  | node : IT → Nat → Nat → IT → IT

@[expose] noncomputable def IT.find (t : IT) (x d : Nat) : Nat :=
  IT.rec (motive := fun _ => Nat) d
    (fun _ k v _ il ir => nIf(Nat.beq x k, v, nIf(Nat.blt x k, il, ir))) t

@[expose] noncomputable def bt (dp : Nat) : List (Nat × Nat) → IT × List (Nat × Nat) :=
  Nat.rec (motive := fun _ => List (Nat × Nat) → IT × List (Nat × Nat))
    (fun xs => (IT.leaf, xs))
    (fun _ ih xs =>
      (fun p => List.rec (motive := fun _ => IT × List (Nat × Nat)) (p.1, [])
        (fun kv rest _ => (fun q => (IT.node p.1 kv.1 kv.2 q.1, q.2)) (ih rest)) p.2) (ih xs)) dp

@[expose] noncomputable def idxT (l : List (Nat × Nat)) : IT := (bt (nat_lit 16) l).1

@[expose] noncomputable def posPairs (E : List Nat) : Nat → List (Nat × Nat) :=
  List.rec (motive := fun _ => Nat → List (Nat × Nat)) (fun _ => [])
    (fun x _ ih s => (s, x) :: ih (Nat.succ s)) E

@[expose] noncomputable def posT (E : List Nat) : IT := idxT (posPairs E (nat_lit 0))

@[expose] noncomputable def sortedK (l : List (Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun a rest ih => List.rec (motive := fun _ => Bool) true
      (fun b _ _ => bAnd(Nat.blt a.1 b.1, ih)) rest) l

@[expose] noncomputable def ixAllK (T : IT) (n : Nat) (E : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih i => strictB i fun i => bAnd(Nat.beq (T.find x n) i, ih (Nat.succ i))) E

@[expose] noncomputable def ixOK (S : List (Nat × Nat)) (E : List Nat) : Bool :=
  bAnd(bAnd(sortedK S, bAnd(Nat.beq S.length E.length, Nat.ble S.length (nat_lit 65535))),
    ixAllK (idxT S) E.length E (nat_lit 0))

@[expose] noncomputable def invK (T : IT) (n : Nat) (E inv : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun inv => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) inv)
    (fun x _ ih inv => List.rec (motive := fun _ => Bool) false
      (fun j inv' _ => andK (Nat.beq (T.find (invGo x n x) n) j) (ih inv')) inv) E inv

@[expose] noncomputable def bfsGen (ix : Nat → Nat) (x i : Nat)
    (k : Nat → List Nat → List (Nat × Nat) → Bool) (gs : List Nat) :
    Nat → Nat → List Nat → List (Nat × Nat) → Bool :=
  List.rec (motive := fun _ => Nat → Nat → List Nat → List (Nat × Nat) → Bool)
    (fun _ c Er Pr => k c Er Pr)
    (fun g _ ih j c Er Pr =>
      strictB (mulF x g) fun y => strictB (ix y) fun t =>
        bIf(Nat.blt t c, ih (Nat.succ j) c Er Pr,
          bAnd(Nat.beq t c,
            List.rec (motive := fun _ => Bool) false
              (fun e Er' _ => List.rec (motive := fun _ => Bool) false
                (fun p Pr' _ => bAnd(bAnd(Nat.beq e y, bAnd(Nat.beq p.1 i, Nat.beq p.2 j)),
                  ih (Nat.succ j) (Nat.succ c) Er' Pr')) Pr) Er))) gs

@[expose] noncomputable def bfsRun (ix : Nat → Nat) (gs : List Nat) (n : Nat) (xs : List Nat) :
    Nat → Nat → List Nat → List (Nat × Nat) → Bool :=
  List.rec (motive := fun _ => Nat → Nat → List Nat → List (Nat × Nat) → Bool)
    (fun _ c _ _ => Nat.beq c n)
    (fun x _ ih i c Er Pr => strictB i fun i => strictB c fun c =>
      bAnd(Nat.blt i c,
        bfsGen ix x i (fun c Er Pr => ih (Nat.succ i) c Er Pr) gs (nat_lit 0) c Er Pr)) xs

@[expose] noncomputable def bfsOK (ix : Nat → Nat) (gs E : List Nat) (P : List (Nat × Nat)) :
    Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun e Er _ => List.rec (motive := fun _ => Bool) false
      (fun p Pr _ => bAnd(bAnd(Nat.beq e oneF, bAnd(Nat.beq p.1 (nat_lit 0),
          Nat.beq p.2 (nat_lit 0))),
        bAnd(Nat.beq P.length E.length,
          bfsRun ix gs E.length E (nat_lit 0) (nat_lit 1) Er Pr))) P) E

end CFSG.KC.C690

end
