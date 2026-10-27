module

public import Init

public section

namespace CFSG.KC.QTwoD6K

@[expose] noncomputable def andB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) false b a

@[expose] noncomputable def orB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) b true a

@[expose] noncomputable def notB (a : Bool) : Bool := Bool.rec (motive := fun _ => Bool) true false a

@[expose] noncomputable def ifB (c t e : Bool) : Bool := Bool.rec (motive := fun _ => Bool) e t c

@[expose] noncomputable def ifN (c : Bool) (t e : Nat) : Nat := Bool.rec (motive := fun _ => Nat) e t c

@[expose] noncomputable def letN (y : Nat) (k : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def letB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def allN (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i ih => andB (f i) ih) n

@[expose] noncomputable def pM (x : Nat) : Nat := Nat.land x 127

@[expose] noncomputable def nM (x : Nat) : Nat := Nat.land (Nat.shiftRight x 7) 127

@[expose] noncomputable def addV (x y : Nat) : Nat :=
  letN (pM x) fun xp => letN (nM x) fun xn => letN (pM y) fun yp => letN (nM y) fun yn =>
  letN (Nat.xor 127 (Nat.lor xp xn)) fun xz => letN (Nat.xor 127 (Nat.lor yp yn)) fun yz =>
    Nat.lor (Nat.lor (Nat.lor (Nat.land xp yz) (Nat.land xz yp)) (Nat.land xn yn))
      (Nat.shiftLeft (Nat.lor (Nat.lor (Nat.land xn yz) (Nat.land xz yn)) (Nat.land xp yp)) 7)

@[expose] noncomputable def negV (x : Nat) : Nat := Nat.lor (nM x) (Nat.shiftLeft (pM x) 7)

@[expose] noncomputable def pc7 (x : Nat) : Nat :=
  Nat.add (Nat.land x 1) <| Nat.add (Nat.land (Nat.shiftRight x 1) 1) <|
  Nat.add (Nat.land (Nat.shiftRight x 2) 1) <| Nat.add (Nat.land (Nat.shiftRight x 3) 1) <|
  Nat.add (Nat.land (Nat.shiftRight x 4) 1) <| Nat.add (Nat.land (Nat.shiftRight x 5) 1)
    (Nat.land (Nat.shiftRight x 6) 1)

@[expose] noncomputable def dotK (a v : Nat) : Nat :=
  letN (pM a) fun ap => letN (nM a) fun an => letN (pM v) fun vp => letN (nM v) fun vn =>
    Nat.mod (Nat.add (pc7 (Nat.lor (Nat.land ap vp) (Nat.land an vn)))
      (Nat.mul 2 (pc7 (Nat.lor (Nat.land ap vn) (Nat.land an vp))))) 3

@[expose] noncomputable def axpy (v c w : Nat) : Nat :=
  ifN (Nat.beq c 0) v (ifN (Nat.beq c 1) (addV v (negV w)) (addV v w))

@[expose] noncomputable def lowbit (x : Nat) : Nat := Nat.xor x (Nat.land x (Nat.sub x 1))

@[expose] noncomputable def normV (v : Nat) : Nat :=
  ifN (Nat.beq (Nat.land (nM v) (lowbit (Nat.lor (pM v) (nM v)))) 0) v (negV v)

@[expose] noncomputable def hK (t : Nat) : Nat := Nat.land t 16383

@[expose] noncomputable def aK (t : Nat) : Nat := Nat.land (Nat.shiftRight t 14) 16383

@[expose] noncomputable def mkR (h a : Nat) : Nat := Nat.lor h (Nat.shiftLeft a 14)

@[expose] noncomputable def normR (t : Nat) : Nat :=
  letN (hK t) fun h =>
    ifN (Nat.beq (Nat.land (nM h) (lowbit (Nat.lor (pM h) (nM h)))) 0) t
      (mkR (negV h) (negV (aK t)))

@[expose] noncomputable def conjK (s t : Nat) : Nat :=
  letN (hK t) fun h => letN (aK t) fun a => letN (hK s) fun sh => letN (aK s) fun sa =>
    normR (mkR (axpy h (dotK sa h) sh) (axpy a (dotK a sh) sa))

@[expose] noncomputable def vecK (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun c _ ih k => Nat.lor (ifN (Nat.beq c 1) (Nat.shiftLeft 1 k)
      (ifN (Nat.beq c 2) (Nat.shiftLeft 1 (Nat.add k 7)) 0)) (ih (Nat.succ k))) l 0

@[expose] noncomputable def genU (r i : Nat) : Nat :=
  ifN (Nat.beq i 0) (normR (mkR (vecK [0, 2, 1, 0, 0, 0, 0]) (vecK [0, 2, 1, 0, 0, 0, 0]))) <|
  ifN (Nat.beq i 1) (normR (mkR (vecK [0, 0, 2, 1, 0, 0, 0]) (vecK [0, 0, 2, 1, 0, 0, 0]))) <|
  ifN (Nat.beq i 2) (normR (mkR (vecK [0, 0, 0, 2, 1, 0, 0]) (vecK [0, 0, 0, 2, 1, 0, 0]))) <|
  ifN (Nat.beq i 3) (normR (mkR (vecK [0, 0, 0, 0, 2, 1, 0]) (vecK [0, 0, 0, 0, 2, 1, 0]))) <|
  ifN (Nat.beq i 4) (normR (mkR (vecK [0, 1, 1, 1, 1, 0, 0]) (vecK [0, 2, 2, 2, 2, 1, 1]))) <|
  ifN (Nat.beq i 5) (normR (mkR (vecK [0, 0, 0, 0, 0, 2, 1]) (vecK [0, 0, 0, 0, 0, 2, 1]))) r

@[expose] noncomputable def wordF (r : Nat) (fuel : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun t _ => t)
    (fun _ ih t w => ifN (Nat.beq w 0) t
      (letN (conjK (genU r (Nat.sub (Nat.mod w 8) 1)) t) fun t' => ih t' (Nat.div w 8))) fuel

@[expose] noncomputable def wordK (r g w : Nat) : Nat := wordF r 20 (genU r g) w

@[expose] noncomputable def tvK (t₁ t₂ : Nat) : Bool :=
  andB (notB (Nat.beq t₁ t₂))
    (orB (Nat.beq (hK t₁) (hK t₂)) (Nat.beq (normV (aK t₁)) (normV (aK t₂))))

@[expose] noncomputable def cRow (i : Nat) : Nat :=
  ifN (Nat.beq i 0) (vecK [0, 0, 1, 1, 1, 1, 1]) <| ifN (Nat.beq i 1) (vecK [0, 1, 0, 1, 1, 1, 1]) <|
  ifN (Nat.beq i 2) (vecK [0, 1, 1, 0, 1, 1, 1]) <| ifN (Nat.beq i 3) (vecK [0, 1, 1, 1, 0, 1, 1]) <|
  ifN (Nat.beq i 4) (vecK [0, 1, 1, 1, 1, 0, 1]) (vecK [0, 2, 2, 2, 2, 2, 0])

@[expose] noncomputable def dRow (i : Nat) : Nat :=
  ifN (Nat.beq i 0) (vecK [0, 1, 2, 2, 2, 2, 2]) <| ifN (Nat.beq i 1) (vecK [0, 2, 1, 2, 2, 2, 2]) <|
  ifN (Nat.beq i 2) (vecK [0, 2, 2, 1, 2, 2, 2]) <| ifN (Nat.beq i 3) (vecK [0, 2, 2, 2, 1, 2, 2]) <|
  ifN (Nat.beq i 4) (vecK [0, 2, 2, 2, 2, 1, 2]) (vecK [0, 1, 1, 1, 1, 1, 2])

@[expose] noncomputable def epsBit (d i : Nat) : Nat :=
  ifN (Nat.beq d 1) (Nat.shiftLeft 1 (Nat.succ i)) (ifN (Nat.beq d 2) (Nat.shiftLeft 1 (Nat.add i 8)) 0)

@[expose] noncomputable def epsK (row : Nat → Nat) (v : Nat) : Nat :=
  Nat.lor (epsBit (dotK (row 0) v) 0) <| Nat.lor (epsBit (dotK (row 1) v) 1) <|
  Nat.lor (epsBit (dotK (row 2) v) 2) <| Nat.lor (epsBit (dotK (row 3) v) 3) <|
  Nat.lor (epsBit (dotK (row 4) v) 4) (epsBit (dotK (row 5) v) 5)

@[expose] noncomputable def suppRow (he ae i : Nat) : Nat :=
  letN (Nat.shiftLeft 1 (Nat.succ i)) fun e =>
    letN (axpy e (dotK e he) ae) fun row => Nat.lor (pM row) (nM row)

@[expose] noncomputable def oneBit (x : Nat) : Bool :=
  andB (notB (Nat.beq x 0)) (Nat.beq (Nat.land x (Nat.sub x 1)) 0)

@[expose] noncomputable def monoK (t : Nat) : Bool :=
  letB (epsK cRow (hK t)) fun he => letB (epsK dRow (aK t)) fun ae =>
    andB (allN 6 fun i => oneBit (suppRow he ae i)) <|
      Nat.beq (Nat.lor (suppRow he ae 0) <| Nat.lor (suppRow he ae 1) <| Nat.lor (suppRow he ae 2) <|
        Nat.lor (suppRow he ae 3) <| Nat.lor (suppRow he ae 4) (suppRow he ae 5)) 126

@[expose] noncomputable def hlK (t : Nat) : Bool :=
  andB (Nat.beq (Nat.land (aK t) 129) 0)
    (orB (notB (Nat.beq (Nat.land (hK t) 129) 0)) (notB (monoK t)))

@[expose] noncomputable def validV (x : Nat) : Bool :=
  andB (Nat.blt x 16384) (Nat.beq (Nat.land (pM x) (nM x)) 0)

@[expose] noncomputable def memL (i : Nat) (S : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun j _ ih => orB (Nat.beq i j) ih) S

@[expose] noncomputable def rowK (y : Nat) (F : Nat → Nat) (S : List Nat) (i kind g₁ w₁ g₂ w₂ : Nat) :
    Bool :=
  letB (F i) fun f => letB (hK f) fun h => letB (aK f) fun a =>
    andB (Nat.blt f 268435456) <| andB (validV h) <| andB (validV a) <|
    andB (Nat.beq (dotK a h) 2) <| andB (Nat.beq (dotK a y) 0) <|
    andB (Nat.beq (Nat.land a 129) 1) <|
    letB (normR f) fun r =>
      ifB (Nat.beq kind 0) (tvK (wordK r g₁ w₁) (wordK r g₂ w₂)) <|
        ifB (Nat.beq kind 1) (hlK (wordK r g₁ w₁)) (andB (Nat.beq kind 2) (memL i S))

end CFSG.KC.QTwoD6K

end
