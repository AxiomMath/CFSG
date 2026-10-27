module

public import Certificates.Data.Kernel.Sym6Sq

public section

namespace CFSG.KC.QdOm

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.W CFSG.KC.LQT.Syl CFSG.KC.Sym6Sq

@[expose] noncomputable def fmK : Nat := nat_lit 2630462966117503262

@[expose] noncomputable def clsK (k : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat) (nat_lit 2) (nat_lit 1)
      (Nat.blt (nat_lit 0) (Nat.land fmK (Nat.shiftLeft (nat_lit 1) k))))
    (nat_lit 0) (Nat.beq k (nat_lit 0))

@[expose] noncomputable def lane (T s : Nat) : Nat := Nat.land (Nat.shiftRight T s) (nat_lit 63)

@[expose] noncomputable def dbl (T y r w : Nat) : Nat :=
  Nat.lor T (Nat.shiftLeft (Nat.xor T (Nat.mul y r)) w)

@[expose] noncomputable def tab4 (a1 b1 a2 b2 : Nat) : Nat :=
  dbl (dbl (dbl (dbl (nat_lit 0) a1 (nat_lit 1) (nat_lit 6)) b1 (nat_lit 65) (nat_lit 12))
    a2 (nat_lit 266305) (nat_lit 24)) b2 (nat_lit 4467856773185) (nat_lit 48)

@[expose] noncomputable def d16 : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

@[expose] noncomputable def tabOK (T a1 b1 a2 b2 : Nat) : Bool :=
  allL d16 fun v => Nat.beq (lane T (Nat.mul (nat_lit 6) v)) (linK [a1, b1, a2, b2] v)

@[expose] noncomputable def chkL (T x off : Nat) : Bool :=
  allL d16 fun v =>
    Nat.beq (clsK (Nat.xor (lane T (Nat.mul (nat_lit 6) v)) x)) (clsK (Nat.add v off))

@[expose] noncomputable def psiP : Nat :=
  nat_lit 26258529960472250484623990635216430637998962648569805787308138193490782982807008279648971334285595532247297572737216

@[expose] noncomputable def psiIP : Nat :=
  nat_lit 13153389583868813439888820855607030182925494708459527611837938568912989508787256383883920871272880879049742326444160

@[expose] noncomputable def conK (Q T a1 b1 a2 b2 a3 b3 : Nat) : Bool :=
  andB (Nat.beq (lane T (nat_lit 18)) (lane Q (Nat.mul (nat_lit 6) a1)))
  (andB (Nat.beq (lane T (nat_lit 6)) (lane Q (Nat.mul (nat_lit 6) b1)))
  (andB (Nat.beq (lane T (nat_lit 72)) (lane Q (Nat.mul (nat_lit 6) a2)))
  (andB (Nat.beq (lane T (nat_lit 24)) (lane Q (Nat.mul (nat_lit 6) b2)))
  (andB (Nat.beq (Nat.xor a3 b3) (lane Q (Nat.mul (nat_lit 6) a3)))
    (Nat.beq a3 (lane Q (Nat.mul (nat_lit 6) b3)))))))

@[expose] noncomputable def plK : List (Nat × Nat) :=
  [(1, 2), (1, 3), (2, 1), (2, 3), (3, 1), (3, 2), (4, 8), (4, 12), (8, 4), (8, 12), (12, 4),
    (12, 8), (16, 32), (16, 48), (22, 43), (22, 61), (25, 46), (25, 55), (31, 37), (31, 58),
    (32, 16), (32, 48), (37, 31), (37, 58), (43, 22), (43, 61), (46, 25), (46, 55), (48, 16),
    (48, 32), (55, 25), (55, 46), (58, 31), (58, 37), (61, 22), (61, 43)]

@[expose] noncomputable def plA : List (Nat × Nat) :=
  [(1, 2), (1, 3), (2, 1), (2, 3), (3, 1), (3, 2), (4, 8), (4, 12), (8, 4), (8, 12), (12, 4),
    (12, 8), (16, 32), (16, 48), (22, 43), (22, 61), (25, 46), (25, 55)]

@[expose] noncomputable def plB : List (Nat × Nat) :=
  [(31, 37), (31, 58), (32, 16), (32, 48), (37, 31), (37, 58), (43, 22), (43, 61), (46, 25),
    (46, 55), (48, 16), (48, 32), (55, 25), (55, 46), (58, 31), (58, 37), (61, 22), (61, 43)]

@[expose] noncomputable def allPr (L : List (Nat × Nat)) (f : Nat → Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun p _ ih => andB (Prod.rec (motive := fun _ => Bool) (fun a b => f a b) p) ih) L

@[expose] noncomputable def memPr (a b : Nat) (L : List (Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun p _ ih => orB (Prod.rec (motive := fun _ => Bool)
      (fun x y => andB (Nat.beq x a) (Nat.beq y b)) p) ih) L

@[expose] noncomputable def covK : Bool :=
  allN (nat_lit 64) fun a => impB (Nat.beq (clsK a) (nat_lit 1)) (allN (nat_lit 64) fun b =>
    impB (andB (Nat.beq (clsK b) (nat_lit 1)) (Nat.beq (clsK (Nat.xor a b)) (nat_lit 1)))
      (memPr a b plK))

@[expose] noncomputable def enum3 (Q1 Q2 T a1 b1 a2 b2 : Nat) (L : List (Nat × Nat)) : Bool :=
  allPr L fun a3 b3 => strictA (Nat.xor a3 b3) fun c3 =>
    impB (andB (chkL T a3 (nat_lit 16)) (andB (chkL T b3 (nat_lit 32)) (chkL T c3 (nat_lit 48))))
      (orB (conK Q1 T a1 b1 a2 b2 a3 b3) (conK Q2 T a1 b1 a2 b2 a3 b3))

@[expose] noncomputable def enumK (Q1 Q2 : Nat) (O L : List (Nat × Nat)) : Bool :=
  allPr O fun a1 b1 => allPr L fun a2 b2 => strictA (tab4 a1 b1 a2 b2) fun T =>
    andB (tabOK T a1 b1 a2 b2)
      (impB (chkL T (nat_lit 0) (nat_lit 0)) (enum3 Q1 Q2 T a1 b1 a2 b2 L))

@[expose] noncomputable def allI (L : List Nat) (test : Nat → Nat → Bool) (k : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih k => andB (test x k) (strictA (Nat.succ k) ih)) L k

@[expose] noncomputable def omRun (om omi : Nat) (E QL : List Nat) : Bool :=
  andB (Nat.beq (mul 24 (mul 24 om om) om) (one 24))
    (andB (allL E fun s => impB (Nat.beq (mul 24 (mul 24 om s) omi) s) (Nat.beq s (one 24)))
      (allI QL (fun x k =>
        andB (Nat.beq (mul 24 (mul 24 om x) omi)
            (getK QL (lane psiP (Nat.mul (nat_lit 6) k)) (one 24)))
          (Nat.beq (mul 24 (mul 24 omi x) om)
            (getK QL (lane psiIP (Nat.mul (nat_lit 6) k)) (one 24)))) (nat_lit 0)))

@[expose] noncomputable def qbIdx : List Nat := [26, 47, 29, 38, 23, 41]

@[expose] noncomputable def omK (G : List Nat) (rgw bw : List (List Int)) (wO : List Int) : Bool :=
  forceA (lstK 24 6 (rlGK 24 G rgw bw)) fun E =>
    forceA (lstK 24 6 (qbIdx.map fun j => getK E j (one 24))) fun QL =>
      strictA (evalZK 24 G wO) fun om => strictA (inv 24 om) fun omi => omRun om omi E QL

end CFSG.KC.QdOm

end
