module

public import Certificates.Data.Kernel.S1277KML

public section

namespace CFSG.KC.S1277Q

open CFSG.KC.S1277ML

@[expose] noncomputable def fld (t w i : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight t (Nat.mul w i)) (Nat.sub (Nat.shiftLeft (nat_lit 1) w) (nat_lit 1))

@[expose] noncomputable def oPtsN : ℕ := nat_lit 49280254209

@[expose] noncomputable def prmN (T p i : ℕ) : ℕ := fld T (nat_lit 3) (appQ p (fld oPtsN (nat_lit 6) i))

@[expose] noncomputable def exN (k : ℕ) : ℕ := fld (nat_lit 16269840) (nat_lit 4) k

@[expose] noncomputable def act4T (y0 m j yj : ℕ) : ℕ :=
  Nat.mul (bit1 m j) (Nat.xor (exN y0) (exN yj))

@[expose] noncomputable def act4P (T p m : ℕ) : ℕ :=
  (fun y0 => Nat.xor (Nat.xor (Nat.xor (act4T y0 m (nat_lit 0) (prmN T p (nat_lit 1)))
      (act4T y0 m (nat_lit 1) (prmN T p (nat_lit 2))))
      (act4T y0 m (nat_lit 2) (prmN T p (nat_lit 3))))
      (act4T y0 m (nat_lit 3) (prmN T p (nat_lit 4))))
    (prmN T p (nat_lit 0))

@[expose] noncomputable def fix4P (T p : ℕ) : ℕ :=
  maskBelow (fun m => Nat.beq (act4P T p m) m) (nat_lit 16)

@[expose] noncomputable def fix6 (T p : ℕ) : Bool :=
  allBelow (fun i => Nat.beq (prmN T p i) i) (nat_lit 6)

@[expose] noncomputable def memZ (p : ℕ) : Bool :=
  orB (Nat.beq p (nat_lit 34630287489))
    (orB (Nat.beq p (nat_lit 52079657154)) (Nat.beq p (nat_lit 17986273347)))

@[expose] noncomputable def kerChk (T : ℕ) (Q : List ℕ) : Bool :=
  allL (fun p => andB (Nat.blt p (nat_lit 68719476736)) (orB (notB (fix6 T p)) (memZ p))) Q

@[expose] noncomputable def packL (w : ℕ) (l : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) (nat_lit 0) (fun x _ r => Nat.lor x (Nat.shiftLeft r w)) l

@[expose] noncomputable def compP (p q : ℕ) : ℕ :=
  Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (appQ p (Nat.land q (nat_lit 63)))
    (Nat.shiftLeft (appQ p (fldN q (nat_lit 6))) (nat_lit 6)))
    (Nat.shiftLeft (appQ p (fldN q (nat_lit 12))) (nat_lit 12)))
    (Nat.shiftLeft (appQ p (fldN q (nat_lit 18))) (nat_lit 18)))
    (Nat.shiftLeft (appQ p (fldN q (nat_lit 24))) (nat_lit 24)))
    (Nat.shiftLeft (appQ p (fldN q (nat_lit 30))) (nat_lit 30))

@[expose] noncomputable def commP (p q : ℕ) : Bool := Nat.beq (compP p q) (compP q p)

@[expose] noncomputable def posMask (f : ℕ → Bool) (l : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun _ => nat_lit 0)
    (fun x _ r i => Nat.lor (Bool.rec (motive := fun _ => ℕ) (nat_lit 0)
      (Nat.shiftLeft (nat_lit 1) i) (f x)) (r (Nat.succ i))) l (nat_lit 0)

@[expose] noncomputable def posOf (q : ℕ) (l : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun _ => nat_lit 255)
    (fun x _ r i => Bool.rec (motive := fun _ => ℕ) (r (Nat.succ i)) i (Nat.beq x q)) l (nat_lit 0)

@[expose] noncomputable def ptRow (IP : List ℕ) (p cm : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun _ => nat_lit 0)
    (fun q _ r j => Nat.lor (Bool.rec (motive := fun _ => ℕ) (nat_lit 255) (posOf (compP p q) IP)
      (bitN cm j)) (Nat.shiftLeft (r (Nat.succ j)) (nat_lit 8))) IP (nat_lit 0)

@[expose] noncomputable def ptAll (IP : List ℕ) (cmN : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun _ => nat_lit 0)
    (fun p _ r i => Nat.lor (ptRow IP p (fld cmN (nat_lit 136) i))
      (Nat.shiftLeft (r (Nat.succ i)) (nat_lit 1088))) IP (nat_lit 0)

structure QT where
  n : ℕ
  ipN : ℕ
  fvN : ℕ
  f4N : ℕ
  cmN : ℕ
  ptN : ℕ

@[expose] noncomputable def ptQ (t : QT) (i j : ℕ) : ℕ :=
  fld t.ptN (nat_lit 8) (Nat.add (Nat.mul (nat_lit 136) i) j)

@[expose] noncomputable def kStep (t : QT) (i j kij pi pj pij vij wij cij k : ℕ) : Bool :=
  strictB (fld t.ipN (nat_lit 36) k) fun pk =>
  orB (Nat.beq pk pi) <| orB (Nat.beq pk pj) <| orB (Nat.beq pk pij) <|
  orB (Nat.beq pk (nat_lit 34630287489)) <|
  andB (Nat.blt (Nat.mul (Nat.mul (pcN (Nat.land vij (fld t.fvN (nat_lit 64) k)))
    (pcN (Nat.land wij (fld t.f4N (nat_lit 16) k)))) (nat_lit 64)) (nat_lit 1024)) <|
  strictB (Nat.land cij (fld t.cmN (nat_lit 136) k)) fun cijk =>
  Nat.beq (Nat.land cijk (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor
    (Nat.shiftLeft (nat_lit 1) i) (Nat.shiftLeft (nat_lit 1) j))
    (Nat.shiftLeft (nat_lit 1) kij)) (Nat.shiftLeft (nat_lit 1) k))
    (Nat.shiftLeft (nat_lit 1) (ptQ t i k))) (Nat.shiftLeft (nat_lit 1) (ptQ t j k)))
    (Nat.shiftLeft (nat_lit 1) (ptQ t kij k)))) cijk

@[expose] noncomputable def jStep (t : QT) (i pi vi wi ci : ℕ) (row : List ℕ) (j : ℕ) : Bool :=
  strictB (fld t.ipN (nat_lit 36) j) fun pj => orB (Nat.beq pj pi) <|
  strictB (Nat.land vi (fld t.fvN (nat_lit 64) j)) fun vij =>
  strictB (Nat.land wi (fld t.f4N (nat_lit 16) j)) fun wij =>
  strictB (Nat.land ci (fld t.cmN (nat_lit 136) j)) fun cij =>
  strictB (ptQ t i j) fun kij =>
  strictB (fld t.ipN (nat_lit 36) kij) fun pij =>
  andB (Nat.blt kij t.n) <|
  andB (Nat.blt (Nat.mul (Nat.mul (pcN vij) (pcN wij)) (nat_lit 16)) (nat_lit 1024)) <|
  allL (fun k => orB (notB (bitN cij k)) (kStep t i j kij pi pj pij vij wij cij k)) row

@[expose] noncomputable def iStep (t : QT) (i : ℕ) (row : List ℕ) : Bool :=
  strictB (fld t.fvN (nat_lit 64) i) fun vi => strictB (fld t.f4N (nat_lit 16) i) fun wi =>
  strictB (fld t.cmN (nat_lit 136) i) fun ci => strictB (fld t.ipN (nat_lit 36) i) fun pi =>
  andB (Nat.blt (Nat.mul (Nat.mul (pcN vi) (pcN wi)) (nat_lit 4)) (nat_lit 1024)) <|
  allL (jStep t i pi vi wi ci row) row

@[expose] noncomputable def rowsOf (cmN n : ℕ) : List (List ℕ) :=
  Nat.rec (motive := fun _ => List (List ℕ) → List (List ℕ)) (fun acc => acc)
    (fun i r acc => r (bitsBelow (fld cmN (nat_lit 136) i) (nat_lit 136) [] :: acc)) n []

@[expose] noncomputable def allRows (t : QT) (R : List (List ℕ)) (i : ℕ) : Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun row _ r i => andB (iStep t i row) (r (Nat.succ i))) R i

@[expose] noncomputable def qTab (n ipN fvN f4N cmN ptN : ℕ) (R : List (List ℕ)) : Bool :=
  strictB ipN fun ipN => strictB fvN fun fvN => strictB f4N fun f4N => strictB cmN fun cmN =>
  strictB ptN fun ptN =>
  andB (Nat.beq (List.length R) n) (allRows ⟨n, ipN, fvN, f4N, cmN, ptN⟩ R (nat_lit 0))

@[expose] noncomputable def qChkI (T : ℕ) (IP : List ℕ) : Bool :=
  (fun cmN => qTab IP.length (packL (nat_lit 36) IP) (packL (nat_lit 64) (IP.map fixMP))
      (packL (nat_lit 16) (IP.map (fix4P T))) cmN (ptAll IP cmN)
      (rowsOf cmN IP.length))
    (packL (nat_lit 136) (IP.map fun p => posMask (commP p) IP))

@[expose] noncomputable def qChk (T : ℕ) (Q : List ℕ) : Bool :=
  andB (kerChk T Q) (andB (Nat.ble (List.length (filtL isInvP Q)) (nat_lit 136))
    (qChkI T (filtL isInvP Q)))

end CFSG.KC.S1277Q

end
