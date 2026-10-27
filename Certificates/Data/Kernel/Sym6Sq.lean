module

public import Certificates.Data.Kernel.LocalQT.SylL

public section

namespace CFSG.KC.Sym6Sq

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.W CFSG.KC.LQT.Syl

@[expose] noncomputable def strictA {α : Type} (y : Nat) (k : Nat → α) : α :=
  Nat.rec (motive := fun _ => α) (k (nat_lit 0)) (fun m _ => k (Nat.succ m)) y

@[expose] noncomputable def forceA {α : Type} (L : List Nat) (k : List Nat → α) : α :=
  List.rec (motive := fun _ => (List Nat → α) → α) (fun k => k [])
    (fun x _ ih k => strictA x fun y => ih fun L' => k (y :: L')) L k

@[expose] noncomputable def revApp (l r : List (Nat × Nat)) : List (Nat × Nat) :=
  List.rec (motive := fun _ => List (Nat × Nat) → List (Nat × Nat)) (fun r => r)
    (fun x _ ih r => ih (x :: r)) l r

@[expose] noncomputable def key6 (c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.add acc (Nat.mul (img c i) (Nat.pow (nat_lit 6) i))) (nat_lit 6)

@[expose] noncomputable def addK (a b : Nat)
    (st : List (Nat × Nat) × List (Nat × Nat) × Nat) :
    List (Nat × Nat) × List (Nat × Nat) × Nat :=
  Prod.rec (motive := fun _ => List (Nat × Nat) × List (Nat × Nat) × Nat)
    (fun acc rest => Prod.rec (motive := fun _ => List (Nat × Nat) × List (Nat × Nat) × Nat)
      (fun nw mask => strictA (Nat.shiftLeft (nat_lit 1) (key6 b)) fun bit =>
        Bool.rec (motive := fun _ => List (Nat × Nat) × List (Nat × Nat) × Nat)
          (strictA (Nat.lor mask bit) fun m => ((a, b) :: acc, (a, b) :: nw, m))
          (acc, nw, mask) (Nat.blt (nat_lit 0) (Nat.land mask bit))) rest) st

@[expose] noncomputable def genK (gs : List (Nat × Nat)) (p : Nat × Nat)
    (st : List (Nat × Nat) × List (Nat × Nat) × Nat) :
    List (Nat × Nat) × List (Nat × Nat) × Nat :=
  List.rec (motive := fun _ => List (Nat × Nat) × List (Nat × Nat) × Nat →
      List (Nat × Nat) × List (Nat × Nat) × Nat) (fun st => st)
    (fun g _ ih st => Prod.rec (motive := fun _ => List (Nat × Nat) × List (Nat × Nat) × Nat)
      (fun g1 g2 => Prod.rec (motive := fun _ => List (Nat × Nat) × List (Nat × Nat) × Nat)
        (fun p1 p2 => strictA (mul 24 g1 p1) fun a => strictA (mul 6 g2 p2) fun b =>
          ih (addK a b st)) p) g) gs st

@[expose] noncomputable def frK (gs : List (Nat × Nat)) (fr : List (Nat × Nat))
    (st : List (Nat × Nat) × List (Nat × Nat) × Nat) :
    List (Nat × Nat) × List (Nat × Nat) × Nat :=
  List.rec (motive := fun _ => List (Nat × Nat) × List (Nat × Nat) × Nat →
      List (Nat × Nat) × List (Nat × Nat) × Nat) (fun st => st)
    (fun p _ ih st => ih (genK gs p st)) fr st

@[expose] noncomputable def stepK (gs : List (Nat × Nat))
    (st : List (Nat × Nat) × List (Nat × Nat) × Nat) :
    List (Nat × Nat) × List (Nat × Nat) × Nat :=
  Prod.rec (motive := fun _ => List (Nat × Nat) × List (Nat × Nat) × Nat)
    (fun acc rest => Prod.rec (motive := fun _ => List (Nat × Nat) × List (Nat × Nat) × Nat)
      (fun fr mask => Prod.rec (motive := fun _ => List (Nat × Nat) × List (Nat × Nat) × Nat)
        (fun acc' rest' => Prod.rec
          (motive := fun _ => List (Nat × Nat) × List (Nat × Nat) × Nat)
          (fun nw mask' => (acc', revApp nw [], mask')) rest')
        (frK gs fr (acc, [], mask))) rest) st

@[expose] noncomputable def gens (cS cT : Nat) : List (Nat × Nat) :=
  [(cS, nat_lit 172066817), (cT, nat_lit 5377089)]

@[expose] noncomputable def bfsK (cS cT : Nat) : List (Nat × Nat) :=
  Prod.rec (motive := fun _ => List (Nat × Nat)) (fun acc _ => acc)
    (Nat.rec (motive := fun _ => List (Nat × Nat) × List (Nat × Nat) × Nat)
      ([(one 24, one 6)], [(one 24, one 6)], Nat.shiftLeft (nat_lit 1) (key6 (one 6)))
      (fun _ st => stepK (gens cS cT) st) (nat_lit 20))

@[expose] noncomputable def idxK (E : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun a _ ih => Bool.rec (motive := fun _ => Nat) (Nat.succ ih) (nat_lit 0) (Nat.beq a x)) E

@[expose] noncomputable def linK (y : List Nat) (m : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun a _ ih d => Nat.xor (Bool.rec (motive := fun _ => Nat) (nat_lit 0) a
      (Nat.beq (Nat.mod d (nat_lit 2)) (nat_lit 1))) (ih (Nat.div d (nat_lit 2)))) y m

@[expose] noncomputable def fixL (y : List Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun m acc => Nat.add acc (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1)
      (Nat.beq (linK y m) m))) (nat_lit 64)

@[expose] noncomputable def below64 (y : List Nat) : Bool :=
  allL y fun a => Nat.blt a (nat_lit 64)

@[expose] noncomputable def cntK (E B : List Nat) (h hi c : Nat) : Bool :=
  forceA (List.rec (motive := fun _ => List Nat) []
      (fun b _ ih => idxK E (mul 24 (mul 24 h b) hi) :: ih) B) fun y =>
    andB (below64 y) (Nat.beq (fixL y) c)

@[expose] noncomputable def liftK (E B : List Nat) (e o h σ : Nat) : Bool :=
  impB (andB (Nat.blt (idxK E (mul 24 h h)) (nat_lit 64))
      (notB (Nat.blt (idxK E h) (nat_lit 64))))
    (cntK E B h (inv 24 h) (Bool.rec (motive := fun _ => Nat) o e (even 6 σ)))

@[expose] noncomputable def sqRun (E B W : List Nat) (e o : Nat) (T : List (Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun p _ ih => andB (Prod.rec (motive := fun _ => Bool) (fun s σ =>
      impB (Nat.beq (mul 6 σ σ) (one 6))
        (allL W fun w => strictA (mul 24 w s) fun h => liftK E B e o h σ)) p) ih) T

@[expose] noncomputable def normK (E : List Nat) (om : Nat) : Bool :=
  strictA (inv 24 om) fun omi => allL E fun x =>
    andB (Nat.blt (idxK E (mul 24 (mul 24 om x) omi)) (nat_lit 64))
      (Nat.blt (idxK E (mul 24 (mul 24 omi x) om)) (nat_lit 64))

@[expose] noncomputable def sqChk (G : List Nat) (rgw bw : List (List Int)) (wS wT wO : List Int)
    (e o : Nat) : Bool :=
  forceA (rlGK 24 G rgw bw) fun B => forceA (lstK 24 6 B) fun E =>
    strictA (evalZK 24 G wO) fun om => strictA (inv 24 om) fun omi =>
      strictA (evalZK 24 G wS) fun cS => strictA (evalZK 24 G wT) fun cT =>
        sqRun E B [one 24, om, omi] e o (bfsK cS cT)

@[expose] noncomputable def normChk (G : List Nat) (rgw bw : List (List Int)) (wO : List Int) :
    Bool :=
  forceA (lstK 24 6 (rlGK 24 G rgw bw)) fun E => normK E (evalZK 24 G wO)

@[expose] noncomputable def bfsChk (G : List Nat) (wS wT : List Int) : Bool :=
  strictA (evalZK 24 G wS) fun cS => strictA (evalZK 24 G wT) fun cT =>
    andB (Nat.beq (lenK (bfsK cS cT)) (nat_lit 720)) (Nat.beq (mul 24 cS cS) (one 24))

end CFSG.KC.Sym6Sq

end
