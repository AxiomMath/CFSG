module

public import Certificates.Data.Kernel.Spor.Fi24PairK

public section

namespace CFSG.KC.Fi24PairPc

open CFSG.KC CFSG.KC.Loop CFSG.KC.Fi24PairK

@[expose] noncomputable def dec (c : Nat) : Int :=
  Bool.rec (motive := fun _ => Int) (Int.neg (Int.ofNat (Nat.div c (nat_lit 2))))
    (Int.ofNat (Nat.div c (nat_lit 2))) (Nat.beq (Nat.mod c (nat_lit 2)) (nat_lit 0))

@[expose] noncomputable def wdec (w : List Nat) : List Int :=
  List.rec (motive := fun _ => List Int) List.nil (fun c _ ih => List.cons (dec c) ih) w

@[expose] noncomputable def nthLL (l : List (List Nat)) (i : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun a _ ih i => Nat.rec (motive := fun _ => List Nat) a (fun k _ => ih k) i) l i

@[expose] noncomputable def nthL3 (l : List (List (List Nat))) (i : Nat) : List (List Nat) :=
  List.rec (motive := fun _ => Nat → List (List Nat)) (fun _ => List.nil)
    (fun a _ ih i => Nat.rec (motive := fun _ => List (List Nat)) a (fun k _ => ih k) i) l i

@[expose] noncomputable def nthN (l : List Nat) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun a _ ih i => Nat.rec (motive := fun _ => Nat) a (fun k _ => ih k) i) l i

@[expose] noncomputable def lenA {α : Type} (l : List α) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def xW (xs : List (List Nat)) (i : Nat) : List Int := wdec (nthLL xs i)

@[expose] noncomputable def pcW (xs : List (List Nat)) (r : List Nat) : List Int :=
  List.rec (motive := fun _ => List Int) List.nil (fun i _ ih => xW xs i ++ ih) r

@[expose] noncomputable def rep (i e : Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) List.nil (fun _ ih => List.cons i ih) e

@[expose] def cbZ : List Nat := [0, 305530, 5604, 221549, 266275, 186844]

@[expose] noncomputable def eqZ (NV : Nat → Nat → Nat) (u v : List Int) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun b _ ih => bAnd(Nat.beq (apZ NV u b) (apZ NV v b), ih)) cbZ

@[expose] noncomputable def inR (lo hi : Nat) (r : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun i _ ih => andB (andB (Nat.ble lo i) (Nat.blt i hi)) ih) r

@[expose] noncomputable def cjOK (NV : Nat → Nat → Nat) (xs : List (List Nat)) (n j : Nat) :
    Nat → List (List Nat) → Bool :=
  fun k cs => List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun c _ ih k => bAnd(andB (inR (Nat.succ j) n c)
      (eqZ NV (invW (xW xs j) ++ (xW xs k ++ xW xs j)) (pcW xs c)), ih (Nat.succ k))) cs k

@[expose] noncomputable def relOK (NV : Nat → Nat → Nat) (net : Nat → Bool) (xs : List (List Nat))
    (ps : List Nat) (pw : List (List Nat)) (cj : List (List (List Nat))) (n j : Nat) : Bool :=
  andB (andB (dirOK net (xW xs j)) (Nat.blt (nat_lit 0) (nthN ps j)))
    (andB (andB (inR (Nat.succ j) n (nthLL pw j))
        (eqZ NV (pcW xs (rep j (nthN ps j))) (pcW xs (nthLL pw j))))
      (andB (Nat.beq (lenA (nthL3 cj j)) (Nat.sub n (Nat.succ j)))
        (cjOK NV xs n j (Nat.succ j) (nthL3 cj j))))

@[expose] noncomputable def cjOne (NV : Nat → Nat → Nat) (xs : List (List Nat)) (n j k : Nat)
    (c : List Nat) : Bool :=
  andB (inR (Nat.succ j) n c) (eqZ NV (invW (xW xs j) ++ (xW xs k ++ xW xs j)) (pcW xs c))

@[expose] noncomputable def relHd (NV : Nat → Nat → Nat) (net : Nat → Bool) (xs : List (List Nat))
    (ps : List Nat) (pw : List (List Nat)) (cj : List (List (List Nat))) (n j : Nat) : Bool :=
  andB (andB (dirOK net (xW xs j)) (Nat.blt (nat_lit 0) (nthN ps j)))
    (andB (andB (inR (Nat.succ j) n (nthLL pw j))
        (eqZ NV (pcW xs (rep j (nthN ps j))) (pcW xs (nthLL pw j))))
      (Nat.beq (lenA (nthL3 cj j)) (Nat.sub n (Nat.succ j))))

@[expose] noncomputable def pcCk (NV : Nat → Nat → Nat) (net : Nat → Bool) (xs : List (List Nat))
    (ps : List Nat) (pw : List (List Nat)) (cj : List (List (List Nat))) (n g : Nat) : Bool :=
  (fun j k => Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) true (relHd NV net xs ps pw cj n j) (Nat.beq j k))
      (cjOne NV xs n j k (nthLL (nthL3 cj j) (Nat.sub k (Nat.succ j)))) (Nat.blt j k))
    (Nat.div g n) (Nat.mod g n)

@[expose] noncomputable def genOK (NV : Nat → Nat → Nat) (net : Nat → Bool) (xs : List (List Nat))
    (n l : Nat) (r : List Nat) : Bool :=
  andB (andB (net l) (inR (nat_lit 0) n r))
    (eqZ NV [Int.ofNat (Nat.add l (nat_lit 3))] (pcW xs r))

@[expose] noncomputable def ckN (M : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => M)
    (fun t ih i => strictN (Nat.shiftRight i (nat_lit 1)) (fun h =>
      nIf(Nat.beq (Nat.land i (nat_lit 1)) (nat_lit 0),
        Nat.land (ih h)
          (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.shiftLeft (nat_lit 1) (Nat.sub (nat_lit 18) t)))
            (nat_lit 1)),
        Nat.shiftRight (ih h) (Nat.shiftLeft (nat_lit 1) (Nat.sub (nat_lit 18) t)))))

@[expose] noncomputable def bitC (m q : Nat) : Nat :=
  nIf(Nat.blt q (nat_lit 524288),
    strictN (Nat.shiftRight q (nat_lit 14)) (fun i =>
      Nat.land (Nat.shiftRight (ckN m (nat_lit 5) i) (Nat.land q (nat_lit 16383))) (nat_lit 1)),
    Nat.land (Nat.shiftRight m q) (nat_lit 1))

@[expose] noncomputable def swpC (d m q : Nat) : Nat :=
  nIf(Nat.beq (bitC m q) (nat_lit 1), Nat.add q d,
    nIf(Nat.ble d q,
      nIf(Nat.beq (bitC m (Nat.sub q d)) (nat_lit 1), Nat.sub q d, q),
      q))

@[expose] noncomputable def ptFC (M : Nat → Nat) (q : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) q
    (fun j ih => strictN ih (fun y => swpC (CFSG.KC.Fi24Net.ldist (Nat.sub (nat_lit 36) j))
      (M (Nat.sub (nat_lit 36) j)) y)) (nat_lit 37)

@[expose] noncomputable def ptRC (M : Nat → Nat) (q : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) q
    (fun j ih => strictN ih (fun y => swpC (CFSG.KC.Fi24Net.ldist j) (M j) y)) (nat_lit 37)

@[expose] noncomputable def ptZC (NW : Nat → Nat → Nat) (z : Int) (x : Nat) : Nat :=
  Int.rec (motive := fun _ => Nat)
    (fun m => nIf(Nat.beq m (nat_lit 0), ptRC (NW (CFSG.KC.Fi24Net.lidx m)) x,
      ptFC (NW (CFSG.KC.Fi24Net.lidx m)) x))
    (fun n => nIf(Nat.beq n (nat_lit 0), ptFC (NW (nat_lit 0)) x,
      ptRC (NW (CFSG.KC.Fi24Net.lidx (Nat.succ n))) x)) z

@[expose] noncomputable def apZC (NW : Nat → Nat → Nat) (w : List Int) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun z _ ih x => strictN (ih x) (fun y => ptZC NW z y)) w x

@[expose] noncomputable def eqZC (NV : Nat → Nat → Nat) (u v : List Int) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun b _ ih => bAnd(Nat.beq (apZC NV u b) (apZC NV v b), ih)) cbZ

@[expose] noncomputable def cjOneC (NV : Nat → Nat → Nat) (xs : List (List Nat)) (n j k : Nat)
    (c : List Nat) : Bool :=
  andB (inR (Nat.succ j) n c) (eqZC NV (invW (xW xs j) ++ (xW xs k ++ xW xs j)) (pcW xs c))

@[expose] noncomputable def relHdC (NV : Nat → Nat → Nat) (net : Nat → Bool) (xs : List (List Nat))
    (ps : List Nat) (pw : List (List Nat)) (cj : List (List (List Nat))) (n j : Nat) : Bool :=
  andB (andB (dirOK net (xW xs j)) (Nat.blt (nat_lit 0) (nthN ps j)))
    (andB (andB (inR (Nat.succ j) n (nthLL pw j))
        (eqZC NV (pcW xs (rep j (nthN ps j))) (pcW xs (nthLL pw j))))
      (Nat.beq (lenA (nthL3 cj j)) (Nat.sub n (Nat.succ j))))

@[expose] noncomputable def pcCkC (NV : Nat → Nat → Nat) (net : Nat → Bool) (xs : List (List Nat))
    (ps : List Nat) (pw : List (List Nat)) (cj : List (List (List Nat))) (n g : Nat) : Bool :=
  (fun j k => Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) true (relHdC NV net xs ps pw cj n j) (Nat.beq j k))
      (cjOneC NV xs n j k (nthLL (nthL3 cj j) (Nat.sub k (Nat.succ j)))) (Nat.blt j k))
    (Nat.div g n) (Nat.mod g n)

@[expose] noncomputable def genOKC (NV : Nat → Nat → Nat) (net : Nat → Bool) (xs : List (List Nat))
    (n l : Nat) (r : List Nat) : Bool :=
  andB (andB (net l) (inR (nat_lit 0) n r))
    (eqZC NV [Int.ofNat (Nat.add l (nat_lit 3))] (pcW xs r))

end CFSG.KC.Fi24PairPc

end
