module

public import Certificates.Data.Kernel.QTwoD6K

public section

namespace CFSG.KC.QTwoD6K

@[expose] noncomputable def foldUpN (n : Nat) (f : Nat → Nat → Nat) (i : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) i (fun j ih => letN ih fun s => f j s) n

@[expose] noncomputable def anyN (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun i ih => orB (f i) ih) n

@[expose] noncomputable def cbitK (c k : Nat) : Nat :=
  ifN (Nat.beq c 1) (Nat.shiftLeft 1 k) (ifN (Nat.beq c 2) (Nat.shiftLeft 1 (Nat.add k 7)) 0)

@[expose] noncomputable def coordK (v j : Nat) : Nat :=
  Nat.add (Nat.land (Nat.shiftRight v j) 1) (Nat.mul 2 (Nat.land (Nat.shiftRight v (Nat.add j 7)) 1))

@[expose] noncomputable def scaleV (c v : Nat) : Nat :=
  ifN (Nat.beq c 1) v (ifN (Nat.beq c 2) (negV v) 0)

@[expose] noncomputable def stepI (F : Nat → Nat) (N code i : Nat) : Nat :=
  ifN (andB (Nat.blt i N) (Nat.beq (F i) code)) (Nat.succ i) (Nat.succ N)

@[expose] noncomputable def covF (keep : Nat → Nat → Bool) (F : Nat → Nat) (N : Nat) (n : Nat) :
    Nat → Nat → Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat → Nat)
    (fun _ _ h a i => ifN (keep h a) (stepI F N (mkR h a) i) i)
    (fun _ ih k lo h a i => foldUpN (Nat.sub 9 lo) (fun j s => letN (Nat.add lo j) fun p =>
      ih (Nat.succ k) p (Nat.lor h (cbitK (Nat.div p 3) k)) (Nat.lor a (cbitK (Nat.mod p 3) k)) s)
      i) n

@[expose] noncomputable def keepL (y h a : Nat) : Bool :=
  andB (Nat.beq (dotK a h) 2) (Nat.beq (dotK a y) 0)

@[expose] noncomputable def covK (y : Nat) (F : Nat → Nat) (N : Nat) : Bool :=
  Nat.beq (foldUpN 3 (fun h₀ s => covF (keepL y) F N 6 1 0 (cbitK h₀ 0) 1 s) 0) N

@[expose] noncomputable def tauC : Nat := mkR 1 128

@[expose] noncomputable def trC : Nat := mkR 8224 8224

@[expose] noncomputable def keepT (h a : Nat) : Bool :=
  andB (keepL 16128 h a) <|
    andB (notB (Nat.beq (mkR h a) tauC)) (notB (Nat.beq (mkR h a) trC))

@[expose] noncomputable def headH (q : Nat) : Nat := ifN (Nat.blt q 2) 0 1

@[expose] noncomputable def headA (q : Nat) : Nat := ifN (Nat.blt q 2) q (Nat.sub q 2)

@[expose] noncomputable def covT (F : Nat → Nat) (N : Nat) : Bool :=
  Nat.beq (foldUpN 5 (fun q s => covF keepT F N 6 1 0 (cbitK (headH q) 0) (cbitK (headA q) 0) s) 0) N

@[expose] noncomputable def genE (e : Nat → Nat) (i : Nat) : Nat :=
  ifN (Nat.blt i 6) (genU 0 i) (e (Nat.sub i 6))

@[expose] noncomputable def ext1 (a : Nat) (_ : Nat) : Nat := a

@[expose] noncomputable def ext2 (a b j : Nat) : Nat := ifN (Nat.beq j 0) a b

@[expose] noncomputable def ext3 (a b c j : Nat) : Nat := ifN (Nat.beq j 0) a (ifN (Nat.beq j 1) b c)

@[expose] noncomputable def wordFE (e : Nat → Nat) (fuel : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun t _ => t)
    (fun _ ih t w => ifN (Nat.beq w 0) t
      (letN (conjK (genE e (Nat.sub (Nat.mod w 16) 1)) t) fun t' => ih t' (Nat.div w 16))) fuel

@[expose] noncomputable def wordE (e : Nat → Nat) (g w : Nat) : Nat := wordFE e 30 (genE e g) w

@[expose] noncomputable def witK (e : Nat → Nat) (kind g₁ w₁ g₂ w₂ : Nat) : Bool :=
  ifB (Nat.beq kind 0) (tvK (wordE e g₁ w₁) (wordE e g₂ w₂))
    (andB (Nat.beq kind 1) (hlK (wordE e g₁ w₁)))

@[expose] noncomputable def nthL (S : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun x _ ih k => Nat.rec (motive := fun _ => Nat) x (fun k' _ => ih k') k) S

@[expose] noncomputable def rowT (F : Nat → Nat) (S : List Nat) (i kind g₁ w₁ g₂ w₂ : Nat) : Bool :=
  letB (F i) fun f => letB (hK f) fun h => letB (aK f) fun a =>
    andB (Nat.blt f 268435456) <| andB (validV h) <| andB (validV a) <|
    andB (Nat.beq (dotK a h) 2) <|
    letB (normR f) fun r =>
      ifB (Nat.beq kind 2) (memL i S) (witK (ext2 tauC r) kind g₁ w₁ g₂ w₂)

@[expose] noncomputable def sigU (j : Nat) : Nat :=
  ifN (Nat.beq j 1) (vecK [0, 0, 2, 2, 2, 2, 1]) <| ifN (Nat.beq j 2) (vecK [0, 2, 0, 2, 2, 2, 1]) <|
  ifN (Nat.beq j 3) (vecK [0, 2, 2, 0, 2, 2, 1]) <| ifN (Nat.beq j 4) (vecK [0, 2, 2, 2, 0, 2, 1]) <|
  ifN (Nat.beq j 5) (vecK [0, 2, 2, 2, 2, 0, 1]) (vecK [0, 0, 0, 0, 0, 0, 1])

@[expose] noncomputable def sigV (v : Nat) : Nat :=
  foldUpN 6 (fun j s => addV s (scaleV (coordK v (Nat.succ j)) (sigU (Nat.succ j)))) 0

@[expose] noncomputable def sigInvK : Bool :=
  allN 6 fun j => Nat.beq (sigV (sigU (Nat.succ j))) (Nat.shiftLeft 1 (Nat.succ j))

@[expose] noncomputable def twLam (k : Nat) : Nat := ifN (Nat.blt k 2) 1 2

@[expose] noncomputable def twC (k : Nat) : Nat := ifN (Nat.beq (Nat.mod k 2) 0) 1 2

@[expose] noncomputable def twV (k v : Nat) : Nat :=
  addV (scaleV (Nat.mod (Nat.mul (twLam k) (coordK v 0)) 3) 1) (scaleV (twC k) (sigV v))

@[expose] noncomputable def twA (k a : Nat) : Nat :=
  foldUpN 6 (fun j s => Nat.lor s
      (cbitK (Nat.mod (Nat.mul (twC k) (dotK a (sigU (Nat.succ j)))) 3) (Nat.succ j)))
    (cbitK (Nat.mod (Nat.mul (twLam k) (coordK a 0)) 3) 0)

@[expose] noncomputable def twR (k t : Nat) : Nat :=
  letN (hK t) fun h => letN (aK t) fun a => normR (mkR (twV k h) (twA k a))

@[expose] noncomputable def applyR (s v : Nat) : Nat := axpy v (dotK (aK s) v) (hK s)

@[expose] noncomputable def applyWF (e : Nat → Nat) (fuel : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun v _ => v)
    (fun _ ih v w => ifN (Nat.beq w 0) v
      (letN (applyR (genE e (Nat.sub (Nat.mod w 16) 1)) v) fun v' => ih v' (Nat.div w 16))) fuel

@[expose] noncomputable def inSpan (p q v : Nat) : Bool :=
  anyN 9 fun c => Nat.beq v (addV (scaleV (Nat.div c 3) p) (scaleV (Nat.mod c 3) q))

@[expose] noncomputable def planeK (e : Nat → Nat) (k w : Nat) : Bool :=
  letB (twV k 1) fun p => letB (twV k 16128) fun q =>
    andB (inSpan p q (applyWF e 30 1 w)) (inSpan p q (applyWF e 30 16128 w))

@[expose] noncomputable def twRowK (tauOk : Bool) (F : Nat → Nat) (S : List Nat)
    (j kind g₁ w₁ g₂ w₂ : Nat) : Bool :=
  letB (normR (F (nthL S (Nat.div j 4)))) fun r => letB (Nat.mod j 4) fun k =>
    ifB (Nat.beq kind 3) (planeK (ext1 r) k w₁) <|
      ifB (Nat.beq kind 4) (andB tauOk (Nat.beq r tauC)) <|
        letB (twR k r) fun t => witK (ext2 r t) kind g₁ w₁ g₂ w₂

@[expose] noncomputable def twRowT (F : Nat → Nat) (S : List Nat) (j kind g₁ w₁ g₂ w₂ : Nat) :
    Bool :=
  letB (normR (F (nthL S (Nat.div j 4)))) fun r => letB (Nat.mod j 4) fun k =>
    ifB (Nat.beq kind 3) (planeK (ext2 tauC r) k w₁) <|
      letB (twR k r) fun t => witK (ext3 tauC r t) kind g₁ w₁ g₂ w₂

end CFSG.KC.QTwoD6K

end
