module

public import Certificates.Data.A8Nbr476

public section

namespace CFSG.KC.A8N476

open Certificates.A8Nbr476

structure V where
  x0 : Nat
  x1 : Nat
  x2 : Nat
  x3 : Nat

structure Q where
  r0 : V
  r1 : V
  r2 : V
  r3 : V

@[expose] noncomputable def dot4 (c0 c1 c2 c3 y0 y1 y2 y3 : Nat) : Nat :=
  Nat.mod (Nat.add (Nat.add (Nat.mul c0 y0) (Nat.mul c1 y1))
    (Nat.add (Nat.mul c2 y2) (Nat.mul c3 y3))) 7

@[expose] noncomputable def linV (a : V) (B : Q) : V :=
  ⟨dot4 a.x0 a.x1 a.x2 a.x3 B.r0.x0 B.r1.x0 B.r2.x0 B.r3.x0,
    dot4 a.x0 a.x1 a.x2 a.x3 B.r0.x1 B.r1.x1 B.r2.x1 B.r3.x1,
    dot4 a.x0 a.x1 a.x2 a.x3 B.r0.x2 B.r1.x2 B.r2.x2 B.r3.x2,
    dot4 a.x0 a.x1 a.x2 a.x3 B.r0.x3 B.r1.x3 B.r2.x3 B.r3.x3⟩

@[expose] noncomputable def mulQ (A B : Q) : Q :=
  ⟨linV A.r0 B, linV A.r1 B, linV A.r2 B, linV A.r3 B⟩

@[expose] noncomputable def idQ : Q := ⟨⟨1, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩⟩

@[expose] noncomputable def subI (A : Q) : Q :=
  ⟨⟨Nat.add A.r0.x0 6, A.r0.x1, A.r0.x2, A.r0.x3⟩, ⟨A.r1.x0, Nat.add A.r1.x1 6, A.r1.x2, A.r1.x3⟩,
    ⟨A.r2.x0, A.r2.x1, Nat.add A.r2.x2 6, A.r2.x3⟩, ⟨A.r3.x0, A.r3.x1, A.r3.x2, Nat.add A.r3.x3 6⟩⟩

@[expose] noncomputable def z7 (x : Nat) : Bool := Nat.beq (Nat.mod x 7) 0

@[expose] noncomputable def zV (v : V) : Bool := z7 v.x0 && z7 v.x1 && z7 v.x2 && z7 v.x3

@[expose] noncomputable def zQ (A : Q) : Bool := zV A.r0 && zV A.r1 && zV A.r2 && zV A.r3

@[expose] noncomputable def e2 (p q r s : Nat) : Bool :=
  Nat.beq (Nat.mod (Nat.mul p s) 7) (Nat.mod (Nat.mul q r) 7)

@[expose] noncomputable def m2 (u v : V) : Bool :=
  e2 u.x0 u.x1 v.x0 v.x1 && e2 u.x0 u.x2 v.x0 v.x2 && e2 u.x0 u.x3 v.x0 v.x3 &&
    e2 u.x1 u.x2 v.x1 v.x2 && e2 u.x1 u.x3 v.x1 v.x3 && e2 u.x2 u.x3 v.x2 v.x3

@[expose] noncomputable def minorsB (A : Q) : Bool :=
  m2 A.r0 A.r1 && m2 A.r0 A.r2 && m2 A.r0 A.r3 && m2 A.r1 A.r2 && m2 A.r1 A.r3 && m2 A.r2 A.r3

@[expose] noncomputable def transvY (Y : Q) : Bool := !zQ Y && zQ (mulQ Y Y) && minorsB Y

@[expose] noncomputable def transvB (X : Q) : Bool := transvY (subI X)

@[expose] noncomputable def inv7 (x : Nat) : Nat := Nat.mod (Nat.pow x 5) 7

@[expose] noncomputable def basQ (a b : Nat) : Q :=
  ⟨⟨a, 1, 1, 1⟩, ⟨0, 1, 6, 0⟩, ⟨0, 0, 1, 6⟩, ⟨1, b, b, b⟩⟩

@[expose] noncomputable def basInvSD (a b s d : Nat) : Q :=
  ⟨⟨Nat.mul s (Nat.mul 3 b), 0, 0, Nat.mul s 4⟩,
    ⟨Nat.mul s 6, Nat.mul s (Nat.mul 2 d), Nat.mul s d, Nat.mul s a⟩,
    ⟨Nat.mul s 6, Nat.mul s (Nat.mul 6 d), Nat.mul s d, Nat.mul s a⟩,
    ⟨Nat.mul s 6, Nat.mul s (Nat.mul 6 d), Nat.mul s (Nat.mul 5 d), Nat.mul s a⟩⟩

@[expose] noncomputable def dQ (a b : Nat) : Nat := Nat.add (Nat.mul a b) 6

@[expose] noncomputable def basInvQ (a b : Nat) : Q :=
  basInvSD a b (inv7 (Nat.mul 3 (dQ a b))) (dQ a b)

@[expose] noncomputable def psiQ (t : Bool) (m : Nat) : Q :=
  Bool.rec (motive := fun _ => Q)
    ⟨⟨1, 0, 0, 0⟩, ⟨0, 1, 6, 0⟩, ⟨0, 0, 1, 6⟩, ⟨0, m, m, m⟩⟩
    ⟨⟨1, 0, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩, ⟨0, m, 0, 0⟩⟩ t

@[expose] noncomputable def psiInvN (t : Bool) (n : Nat) : Q :=
  Bool.rec (motive := fun _ => Q)
    ⟨⟨1, 0, 0, 0⟩, ⟨0, 3, 5, Nat.mul 5 n⟩, ⟨0, 2, 5, Nat.mul 5 n⟩, ⟨0, 2, 4, Nat.mul 5 n⟩⟩
    ⟨⟨1, 0, 0, 0⟩, ⟨0, 0, 0, n⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩⟩ t

@[expose] noncomputable def psiInvQ (t : Bool) (m : Nat) : Q := psiInvN t (inv7 m)

@[expose] noncomputable def wB (i : Nat) : Q :=
  Bool.rec (motive := fun _ => Q)
    (Bool.rec (motive := fun _ => Q)
      ⟨⟨1, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 6⟩⟩
      ⟨⟨1, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, 0, 1⟩, ⟨0, 0, 1, 0⟩⟩ (Nat.beq i 1))
    ⟨⟨1, 0, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, 0, 1⟩⟩ (Nat.beq i 0)

@[expose] noncomputable def wA (i : Nat) : Q :=
  Bool.rec (motive := fun _ => Q)
    (Bool.rec (motive := fun _ => Q)
      ⟨⟨1, 0, 0, 0⟩, ⟨0, 2, 3, 5⟩, ⟨0, 6, 5, 2⟩, ⟨0, 0, 0, 1⟩⟩
      ⟨⟨1, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 1⟩, ⟨0, 0, 0, 6⟩⟩ (Nat.beq i 1))
    ⟨⟨1, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, 6, 0⟩, ⟨0, 0, 1, 1⟩⟩ (Nat.beq i 0)

@[expose] noncomputable def wQ (t : Bool) (i : Nat) : Q := Bool.rec (motive := fun _ => Q) (wB i) (wA i) t

@[expose] noncomputable def genLQ (t : Bool) (a b m i : Nat) : Q :=
  mulQ (mulQ (basInvQ a b) (mulQ (mulQ (psiQ t m) (wQ t i)) (psiInvQ t m))) (basQ a b)

@[expose] noncomputable def genKQ (k : Nat) : Q :=
  Bool.rec (motive := fun _ => Q)
    (Bool.rec (motive := fun _ => Q)
      ⟨⟨1, 0, 0, 0⟩, ⟨0, 2, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩⟩
      ⟨⟨1, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, 0, 1⟩, ⟨0, 0, 1, 0⟩⟩ (Nat.beq k 1))
    ⟨⟨1, 0, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, 0, 1⟩⟩ (Nat.beq k 0)

structure G6 where
  g0 : Q
  g1 : Q
  g2 : Q
  g3 : Q
  g4 : Q
  g5 : Q

@[expose] noncomputable def gensQ (t : Bool) (a b m : Nat) : G6 :=
  ⟨genLQ t a b m 0, genLQ t a b m 1, genLQ t a b m 2, genKQ 0, genKQ 1, genKQ 2⟩

@[expose] noncomputable def pick (G : G6) (l : Nat) : Q :=
  Bool.rec (motive := fun _ => Q)
    (Bool.rec (motive := fun _ => Q)
      (Bool.rec (motive := fun _ => Q)
        (Bool.rec (motive := fun _ => Q)
          (Bool.rec (motive := fun _ => Q) G.g5 G.g4 (Nat.beq l 4)) G.g3 (Nat.beq l 3))
        G.g2 (Nat.beq l 2)) G.g1 (Nat.beq l 1)) G.g0 (Nat.beq l 0)

@[expose] noncomputable def prodQ (G : G6) (w : List (Fin 6)) : Q :=
  List.rec (motive := fun _ => Q) idQ (fun l _ acc => mulQ (pick G l.val) acc) w

@[expose] noncomputable def gensC (c : Case) : G6 := gensQ c.1 c.2.1.val c.2.2.1.val c.2.2.2.val

@[expose] noncomputable def wordB (e : Case × List (Fin 6)) : Bool := transvB (prodQ (gensC e.1) e.2)

@[expose] noncomputable def wordsB (L : List (Case × List (Fin 6))) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun e _ ih => wordB e && ih) L

@[expose] noncomputable def caseCode (c : Case) : Nat :=
  Nat.add (Nat.add (Nat.add (Nat.mul 343 (Bool.rec (motive := fun _ => Nat) 0 1 c.1))
    (Nat.mul 49 c.2.1.val)) (Nat.mul 7 c.2.2.1.val)) c.2.2.2.val

@[expose] noncomputable def codesL {β : Type} (L : List (Case × β)) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun e _ ih => caseCode e.1 :: ih) L

@[expose] noncomputable def codesC (L : List Case) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun c _ ih => caseCode c :: ih) L

@[expose] noncomputable def memN (n : Nat) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun x _ ih => Nat.beq n x || ih) L

@[expose] noncomputable def validN (n : Nat) : Bool :=
  !z7 n && !Nat.beq (Nat.mod (Nat.mul (Nat.mod (Nat.div n 49) 7) (Nat.mod (Nat.div n 7) 7)) 7) 1

@[expose] noncomputable def invB (t : Bool) (a b m : Nat) : Bool :=
  zQ (subI (mulQ (basQ a b) (basInvQ a b))) && zQ (subI (mulQ (basInvQ a b) (basQ a b))) &&
    zQ (subI (mulQ (psiQ t m) (psiInvQ t m))) && zQ (subI (mulQ (psiInvQ t m) (psiQ t m)))

@[expose] noncomputable def okN (W E : List Nat) (n : Nat) : Bool :=
  !validN n || (invB (Nat.beq (Nat.div n 343) 1) (Nat.mod (Nat.div n 49) 7) (Nat.mod (Nat.div n 7) 7)
    (Nat.mod n 7) && (memN n E || memN n W))

@[expose] noncomputable def allBelow (f : Nat → Bool) (N : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun n ih => f n && ih) N

@[expose] noncomputable def coverB (W E : List Nat) : Bool := allBelow (okN W E) 686

@[expose] def V.get (v : V) : Fin 4 → Nat := ![v.x0, v.x1, v.x2, v.x3]

@[expose] def Q.row (A : Q) : Fin 4 → V := ![A.r0, A.r1, A.r2, A.r3]

@[expose] def dec (A : Q) : M4 := Matrix.of fun i j => (((A.row i).get j : Nat) : ZMod 7)

@[expose] noncomputable def rowE (r : List (List (ZMod 7))) (i j : Nat) : Nat :=
  ((r.getD i []).getD j 0).val

@[expose] noncomputable def rowsQ (r : List (List (ZMod 7))) : Q :=
  ⟨⟨rowE r 0 0, rowE r 0 1, rowE r 0 2, rowE r 0 3⟩, ⟨rowE r 1 0, rowE r 1 1, rowE r 1 2, rowE r 1 3⟩,
    ⟨rowE r 2 0, rowE r 2 1, rowE r 2 2, rowE r 2 3⟩, ⟨rowE r 3 0, rowE r 3 1, rowE r 3 2, rowE r 3 3⟩⟩

@[expose] noncomputable def all6 (f : Nat → Bool) : Bool := f 0 && f 1 && f 2 && f 3 && f 4 && f 5

@[expose] noncomputable def monE (e : Case × List (List (ZMod 7)) × List (List (ZMod 7))) : Bool :=
  zQ (subI (mulQ (rowsQ e.2.1) (rowsQ e.2.2))) &&
    all6 fun k => monCubeB (dec (mulQ (mulQ (rowsQ e.2.1) (pick (gensC e.1) k)) (rowsQ e.2.2)))

@[expose] noncomputable def monB (L : List (Case × List (List (ZMod 7)) × List (List (ZMod 7)))) :
    Bool :=
  List.rec (motive := fun _ => Bool) true (fun e _ ih => monE e && ih) L

end CFSG.KC.A8N476
